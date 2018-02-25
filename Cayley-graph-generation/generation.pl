#!/usr/bin/perl

use strict;
use warnings;

use PDL;
use PDL::Matrix;
use PDL::NiceSlice;

use Graph::Directed;
use Graph::Writer::Dot;

use Data::Dumper;
use List::MoreUtils qw( firstidx );

use Devel::Size qw( size total_size );
use Number::Format qw( format_bytes );
use Time::HiRes qw( gettimeofday tv_interval);

use Math::GMPz qw( Rmpz_get_ui );
use Math::Primality qw( next_prime );


sub determinant 
{
	my ($M, $zp) = @_;

	my $det = abs(index2d($M, 0,0) * index2d($M, 1,1) - index2d($M, 0,1) * index2d($M, 1,0));

	return $det % $zp;
}

sub generate_graph
{
	#####
	my @t0 = gettimeofday();
	#####

	my ($keys_ref, $multiplication_results_ref) = @_;
	my $graph = Graph::Undirected->new; 

	foreach my $start_node (@{ $keys_ref }) {
		my @nodes = @{ $multiplication_results_ref->[$start_node->[0]] };
		foreach my $end_node ( @nodes )  {
			$graph->add_edge(make_matrix_label(${start_node}->[1]), make_matrix_label($end_node));
		}
	}

	#####	
	print "Generovanie grafu: " . tv_interval( \@t0 ) . " sekund\n";
	print "Velkost graf: " . format_bytes(total_size(\$graph)) . "\n";
	print "############################################\n";
	#####

	return $graph;
}

sub generate_group
{
	my ($generating_set_ref, $zp) = @_;
	my @generating_set = @{ $generating_set_ref };
	my @stack = @generating_set;
	my @multiplication_results;
	my $current_node = $stack[0]; 
	my @keys = [ get_index($current_node), $current_node ];

	
	#####
	my @t0 = gettimeofday();
	#####
	
	while(@stack) {
		foreach my $generating_element (@generating_set) {
			my $multiplication_result = ($current_node x $generating_element) % $zp;	
			push @{ $multiplication_results[get_index($current_node)] }, $multiplication_result;
			push @stack, $multiplication_result;
		}

		shift @stack;

		while(@stack && defined($multiplication_results[ get_index($stack[0]) ])) {
			shift @stack;
		}

		if(@stack) {
			$current_node = $stack[0];
			push @keys, [ get_index($current_node), $current_node ];
		}
	}

	#####	
	print "Generovanie prvkov: " . tv_interval( \@t0 ) . " sekund\n";
	print "Velkost multiplication_results: " . format_bytes(total_size(\@multiplication_results)) . "\n";
	print "Pocet vrcholov: " . ($#keys + 1) . "\n";
	print "############################################\n";
	#####
	
	return ( \@keys, \@multiplication_results );
}

sub make_matrix_label
{
	my ($A) = @_;

	return "((" .index2d($A, 0,0) . ", " . index2d($A, 0,1) . ")," .
			"(" .index2d($A, 1,0) . ", " . index2d($A, 1,1) . "))";
}

sub get_index
{
	my ($A) = @_;

	return index2d($A, 0,0) . index2d($A, 0,1) . index2d($A, 1,0) . index2d($A, 1,1);
}

sub generate_whole_group 
{
	my ($zp) = @_;

	my @generating_set ;
	my $zpg = $zp - 1;

	foreach my $i (0..$zpg){
		foreach my $j (0..$zpg) {
			foreach my $k (0..$zpg) {
				foreach my $l (0..$zpg) {
					my $m = PDL::Matrix->pdl([[$i, $j],[$k, $l]]);
					if(determinant($m, $zp) != 0) {
						push @generating_set, $m;
					}
				}
			}
		}
	}

	return \@generating_set;
}

sub check_set 
{
	my ($generating_set_ref, $zp) = @_;
	my @generating_set = @{ $generating_set_ref };

	@generating_set = map { $_ % $zp } @generating_set;

	foreach my $generating_element (@generating_set) {
		if((det($generating_element) % $zp) == 0) {
			print "!!!!!!!!!!!!!! Null determinant !!!!!!!!!!!!\n";
			print $generating_element;
			print "\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n";
			exit;
		}
	}

	return \@generating_set;
}

sub compute_order
{
	my ($generating_set_ref, $zp) = @_;
	my @generating_set = @{ $generating_set_ref };

	my $eye = PDL::Matrix->pdl([[1,0],[0,1]]);
	foreach my $generating_element (@generating_set) {
		my $order = 1;
		my $res = $generating_element;
		while(!(all $res == $eye)) {
			$res = ($res x $generating_element) % $zp;
			$order++;
		}
		print "-------\n";
		print "Order of element: $order\n";
		print $generating_element;
	}
}

sub make_graphical_output
{
	my ($graph) = @_;
	my $writer = Graph::Writer::Dot->new();
	$writer->write_graph($graph, 'graf.dot');

	system "circo", "-Tsvg", "graf.dot", "-o", "outfile.svg";
}

sub give_nth_prime 
{
	my ($n) = @_;

	my $prime = 2;
	foreach my $i (2..$n) {
		$prime = next_prime($prime);
	}

	return Rmpz_get_ui $prime;
}

sub order_of_GL
{
	my ($n, $q) = @_;

	my $order = 1;
	foreach my $k (0..$n-1) {
		$order = $order * ($q**$n - $q**$k);
	}

	return $order;
}

my $zp = give_nth_prime(5);

my @generating_set = 
	( 
		PDL::Matrix->pdl([[1,3],[1,6]]), 
	);

print "Order of GL(2,$zp): " . order_of_GL(2,$zp) . "\n";
print "Zp: $zp\n";
print "############################################\n";
make_graphical_output(generate_graph(generate_group(check_set(\@generating_set, $zp), $zp)));
