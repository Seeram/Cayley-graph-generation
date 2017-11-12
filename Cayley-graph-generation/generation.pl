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

sub print_matrix_arr
{
	my (@A) = @_;

	my $counter = 1;
	foreach my $i (@A) {
		print "$counter\t" . make_matrix_label($i) . "\n";
		$counter++;
	}
}

my $zp = 3;
my @generating_set =
	(
		PDL::Matrix->pdl([[0,1],[1,1]]),
		PDL::Matrix->pdl([[0,1],[1,0]]),
	);

@generating_set = map { $_ % $zp } @generating_set;
my @stack = @generating_set;
my @multiplication_results;

foreach my $generating_element (@generating_set) {
	if(det($generating_element) == 0) {
		print "Nulovy determinant !\n";
		print $generating_element;
		exit;
	}
}

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

my $graph = Graph::Undirected->new;

foreach my $start_node (@keys) {
	foreach my $end_node ( @{ $multiplication_results[$start_node->[0]] } )  {
		$graph->add_edge(make_matrix_label(${start_node}->[1]), make_matrix_label($end_node));
	}
}

print "Priemer grafu: " . $graph->diameter(). "\n";
my $writer = Graph::Writer::Dot->new();

$writer->write_graph($graph, 'graf.dot');

system "dot", "-Tps", "graf.dot", "-o", "outfile.ps";
# system "circo", "-Tsvg", "graf.dot", "-o", "outfile.svg";
