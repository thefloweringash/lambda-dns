#!/usr/bin/perl

use warnings;
use strict;


use Data::Dumper;
use Parse::RecDescent;
use Net::DNS::Nameserver;

package Main;

my $domain = "lambda.cons.org.nz";
my $final_ip = "216.218.210.82";

sub reply_handler {
    my ($qname, $qclass, $qtype, $peerhost, $query, $conn) = @_;
    my ($rcode, @ans, @auth, @add);

    my $happy = 0;
    eval {
	if ($qtype eq "A" && $qname eq "nf.lambda.cons.org.nz") {
	    $rcode = "NOERROR";
	    push @ans,
	    Net::DNS::RR->new("nf.$domain 60 $qclass A $final_ip");
	    $happy = 1;
	} elsif ($qtype eq "A" && $qname =~ /^(.*)\.lambda\.cons\.org\.nz$/) {
	    # ugh
	    my $e = $1;
	    $e =~ s/\\\\/\\/g;
	    $e =~ s/\\\(/\(/g;
	    $e =~ s/\\\)/\)/g;
	    my $lambda_expr = Lambda::parse($e);
	    if (defined $lambda_expr) {
		Lambda::to_debruijn($lambda_expr);
		my $changed = Lambda::singlestep($lambda_expr);
		if ($changed) {
		    Lambda::from_debruijn($lambda_expr);
		    my $reduced = Lambda::show($lambda_expr);
		    $reduced =~ s/\\/\\\\/g;
		    $rcode = "NOERROR";
		    push @ans,
		    Net::DNS::RR->new("$qname 60 $qclass CNAME $reduced.$domain");
		} else {
		    $rcode = "NOERROR";
		    push @ans,
		    Net::DNS::RR->new("$qname 60 $qclass CNAME nf.$domain");
		    push @ans,
		    Net::DNS::RR->new("nf.$domain 60 $qclass A $final_ip");
		}
		$happy = 1;
	    }
	}
    };
    unless ($happy) {
	$rcode = "NXDOMAIN";
    }

    return ($rcode, \@ans, \@auth, \@add, { aa => 1 });

}

sub run {
    my $ns = Net::DNS::Nameserver->new(
	LocalPort => 5053,
	ReplyHandler => \&Main::reply_handler,
	Verbose => 0,
	) || die "couldn't create ns";

    $ns->main_loop;
}

package Lambda;

my @all_syms =
    split(//,'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz');

my $grammar = q{
var: /[A-Za-z]/
	{ $return = [ "var", $item[1] ] }

abstraction: "(" ( "\\\\" | "^" ) var "." term ")"
	{ $return = [ "abstraction", $item[3], $item[5] ] }

term: (abstraction | var | bracketed )(s)
	{ $return = Lambda::foldl1(\\&Lambda::app, $item[1]) }

bracketed: "(" term ")"
	{ $return = $item[2] }

toplevel: term /$/
	{ $return = $item[1] }
};

my $parser = new Parse::RecDescent($grammar);

sub app {
    my ($x, $y) = @_;
    [ "application", $x, $y ];
}

sub foldl1 {
    my ($f, $xs) = @_;
    my $x = shift @$xs;
    while (@$xs) {
	$x = &$f($x, shift @$xs);
    }
    $x;
}

sub parse {
    my ($str) = @_;
    $parser->toplevel($str);
}

sub show {
    my ($term) = @_;
    if ($term->[0] eq "abstraction") {
	"(^" . $term->[1][1] . "." .  show($term->[2]) . ")";
    } elsif ($term->[0] eq "var") {
	$term->[1];
    } elsif ($term->[0] eq "application") {
	my $tail;
	if ($term->[2][0] eq "application") {
	    $tail = "(" . show($term->[2]) . ")";
	} else {
	    $tail = show($term->[2]);
	}
	show($term->[1]) . $tail;
    } else {
	die "Invalid lambda term structure";
    }
}

sub singlestep {
    my ($term) = @_;

    if ($term->[0] eq "application") {
	if ($term->[1][0] eq "abstraction")  {
	    substitute($term);
	    return 1;
	} else {
	    my $ret = singlestep($term->[1]);
	    if ($ret == 1) { return 1; };
	    return singlestep($term->[2]);
	}
    } elsif ($term->[0] eq "abstraction") {
	singlestep($term->[2]);
    } else {
	return 0;
    }
}

sub incr_binders {
    my ($binders) = @_;
    +{map { $_ => $binders->{$_}+1 } keys %$binders};
}

sub to_debruijn {
    my ($term, $binders) = @_;
    if (!defined $binders) {
	$binders = {};
    }
    if ($term->[0] eq "application") {
	to_debruijn($term->[1], $binders);
	to_debruijn($term->[2], $binders);
    } elsif ($term->[0] eq "var") {
	my $n = $binders->{$term->[1]} or die "Invalid lambda term";
	$term->[1] = $n;
    } elsif ($term->[0] eq "abstraction") {
	$binders->{$term->[1][1]} = 0;
	$binders = incr_binders($binders);
	to_debruijn($term->[2], $binders);
    }
}

sub from_debruijn {
    my ($term, $bindings) = @_;
    if (!defined $bindings) {
	alpha_fix($term);
	$bindings = [];
    }
    if ($term->[0] eq "application") {
	from_debruijn($term->[1], $bindings);
	from_debruijn($term->[2], $bindings);
    } elsif ($term->[0] eq "var") {
	$term->[1] = $bindings->[$#{$bindings} + 1 - $term->[1]]
	    or die;
    } elsif ($term->[0] eq "abstraction") {
	push @$bindings, $term->[1][1];
	from_debruijn($term->[2], $bindings);
	pop @$bindings;
    }
}

sub substitute {
    my ($app) = @_;
    my $rhs = $app->[2];
    my $body = $app->[1][2];
    substitute_worker($body, 1, $rhs);
    $#{$app} = -1;
    map { push @$app, $_ } @$body;
}

sub alpha_fix {
    my ($term, $bindings, $syms) = @_;
    if (!defined $bindings) {
	$bindings = [];
	$syms = +{map { $_ => undef } @all_syms};
	dfs_walk( sub {
	    my ($term) = @_;
	    if ($term->[0] eq "abstraction") {
		delete $syms->{$term->[1][1]};
	    }}, $term);
	$syms = [keys %$syms];
    }
    if ($term->[0] eq "application") {
	alpha_fix($term->[1], $bindings, $syms);
	alpha_fix($term->[2], $bindings, $syms);
    } elsif ($term->[0] eq "var") {
	my $self = $#{$bindings} + 1 - $term->[1];
	my $binding = $bindings->[$self];
	my @rest = @{$bindings}[$self+1 .. $#{$bindings}];
	for my $outer (@rest) {
	    if ($outer->[1] eq $binding->[1]) {
		$binding->[0][1][1] = pop @$syms;
		last;
	    }
	}
    } elsif ($term->[0] eq "abstraction") {
	push @$bindings, [$term, $term->[1][1]];
	alpha_fix($term->[2], $bindings, $syms);
	pop @$bindings;
    }
}

sub dfs_walk {
    my ($op, $term) = @_;
    &$op($term);
    if ($term->[0] eq "application") {
	dfs_walk($op, $term->[1]);
	dfs_walk($op, $term->[2]);
    } elsif ($term->[0] eq "abstraction") {
	dfs_walk($op, $term->[2]);
    }

}

sub substitute_worker {
    my ($term, $depth, $replacement) = @_;
    if ($term->[0] eq "var") {
	if ($term->[1] == $depth) {
	    $#{$term} = -1;
	    map { push @$term, $_ }
	    @{deep_copy_term_incr_depth($replacement, $depth-1, 0)};
	}
    } elsif ($term->[0] eq "application") {
	substitute_worker($term->[1], $depth, $replacement);
	substitute_worker($term->[2], $depth, $replacement);
    } elsif ($term->[0] eq "abstraction" ) {
	substitute_worker($term->[2], $depth+1, $replacement);
    }
}

sub deep_copy_term_incr_depth {
    my ($term, $depth, $localdepth) = @_;
    if ($term->[0] eq "var") {
	if ($term->[1] > $localdepth) {
	    [ "var", $term->[1]+$depth ];
	} else {
	    [ "var", $term->[1] ];
	}
    } elsif ($term->[0] eq "application") {
	[ "application",
	  deep_copy_term_incr_depth($term->[1], $depth, $localdepth),
	  deep_copy_term_incr_depth($term->[2], $depth, $localdepth) ];
    } elsif ($term->[0] eq "abstraction") {
	[ "abstraction",
	  [@{$term->[1]}],
	  deep_copy_term_incr_depth($term->[2], $depth, $localdepth+1) ];
    }
}

package Test;


sub hack {
#     my $expr = "(\\x.x)(\\x.(\\z.z)x(xy)(\\x.x)z)";
#     my $expr = "(\\z.zz(\\x.xx)(\\y.yy))";
#     my $expr = "(\\x.(\\y.y))(\\z.z)";
    my $expr = "(^y.(^z.(^y.yzyz))(^x.y))";
    my $parsed = Lambda::parse($expr);

#     print ::Dumper($parsed);

#     Lambda::walk_dfs( sub { print Lambda::show($_[0]), "\n" }, $parsed );

    print(Lambda::show($parsed), "\n");
    Lambda::to_debruijn($parsed);
    print(Lambda::show($parsed), "\n");
    Lambda::singlestep($parsed);
    print(Lambda::show($parsed), "\n");
    Lambda::from_debruijn($parsed);
    print(Lambda::show($parsed), "\n");
#     print ::Dumper($parsed);
#     print Lambda::show(Lambda::singlestep($parsed));
#     print ::Dumper(Lambda::parse($expr));
#     print Lambda::show(Lambda::parse("(\\x.x)"));
#     print ::Dumper(Lambda::foldl1(\&Lambda::app, [1,2,3]));
}




# Entry point
if (!defined $ARGV[0]) {
    print "Usage: $0 [ start | test ]\n";
} elsif ($ARGV[0] eq "start") {
    Main::run();
} elsif ($ARGV[0] eq "test") {
    Test::hack();
}
