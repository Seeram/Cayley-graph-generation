#!/usr/bin/perl

use strict;
use warnings;

use PDL;
use PDL::Matrix;
use PDL::NiceSlice;

use Graph::Directed;
use Graph::Writer::Dot;

use List::MoreUtils qw(firstidx); 
use Data::Dumper;
use Devel::Size qw( size total_size );
use Number::Format qw( format_bytes );
use Time::HiRes qw( gettimeofday tv_interval);

### TODO
# splitting file into multiple
# function to compute order of GL(n,q) source wikipedia
# logical split of program 

sub graph_generation
{
	my ($keys_ref, $multiplication_results_ref) = @_;
	my @multiplication_results = @{ $multiplication_results_ref };

	
	my $graph = Graph::Undirected->new;


	foreach my $start_node (@{ $keys_ref }) {
		foreach my $end_node ( @{ $multiplication_results[$start_node->[0]] } )  {
			$graph->add_edge(make_matrix_label(${start_node}->[1]), make_matrix_label($end_node));
		}
	}

	return $graph;
}

sub group_generation
{
	my ($generating_set_ref, $zp) = @_;
	my @generating_set = @{ $generating_set_ref };
	my @stack = @generating_set;
	my @multiplication_results;

	my $current_node = $stack[0]; 
	my @keys = [ get_index($current_node), $current_node ];

	while(@stack) {
		foreach my $generating_element (@generating_set) {
			my $multiplication_result = $current_node x $generating_element % $zp;	
			push @{ $multiplication_results[get_index($current_node)] }, $multiplication_result;
			push @stack, $multiplication_result;
		}

		shift @stack;

		while(@stack && defined($multiplication_results[get_index($stack[0])])) {
			shift @stack;
		}

		if(@stack) {
			$current_node = $stack[0];
			push @keys, [ get_index($current_node), $current_node ];
		}
	}
	print "pocet klucov: $#keys\n";

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

sub generate_set
{
	my ($zp) = @_;

	my @generating_set =
		(
			PDL::Matrix->pdl([[0,1],[1,1]]),
			PDL::Matrix->pdl([[0,1],[1,0]]),
		);
	@generating_set = map { $_ % $zp } @generating_set;

	##my $zpg = $zp - 1;
	##foreach my $i (0..$zpg){
		##foreach my $j (0..$zpg) {
			##foreach my $k (0..$zpg) {
				##foreach my $l (0..$zpg) {
					##my $m = PDL::Matrix->pdl([[$i, $j],[$k, $l]]);
					##if(det($m) != 0) {
						##push @generating_set, $m;
					##}
				##}
			##}
		##}
	##}
	
	foreach my $generating_element (@generating_set) {
		if(det($generating_element) == 0) {
			print "Nulovy determinant !\n";
			print $generating_element;
			exit;
		}
	}

	return \@generating_set;
}

sub make_graphical_output
{
	my ($graph) = @_;
	my $writer = Graph::Writer::Dot->new();
	$writer->write_graph($graph, 'graf.dot');

	system "circo", "-Tsvg", "graf.dot", "-o", "outfile.svg";
	
}

my $zp = 4;
make_graphical_output(graph_generation(group_generation(generate_set($zp), $zp)));
