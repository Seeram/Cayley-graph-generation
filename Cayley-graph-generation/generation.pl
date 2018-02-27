#!/usr/bin/perl

use strict;
use warnings;

use PDL;
use PDL::Matrix;
use PDL::NiceSlice;

use Graph::Directed;
use Graph::Writer::Dot;

use Data::Dumper;

use Devel::Size qw( size total_size );
use Number::Format qw( format_bytes );
use Time::HiRes qw( gettimeofday tv_interval);

use Math::GMPz qw( Rmpz_get_ui );
use Math::Primality qw( next_prime );

# TODO
# Make algorithm for arbitrary Zp with hash function - DONE
# Consider using database instead of alocated data
# Consider paralelization in computing elements of group
# Consider getting rid of PDL
#  - make performance tests for computing multiplication of matrices
# Hash table size computing
#  - not really necessary
# Representing matrices only by its keys
# Consider making structured data for better readability

sub determinant_Zp 
{
	my ($M, $zp) = @_;

	my $det = abs(index2d($M, 0,0) * index2d($M, 1,1) - index2d($M, 0,1) * index2d($M, 1,0));

	return $det % $zp;
}

sub compute_hash 
{
	my ($M, $zp) = @_;

	my $hash = 0;
	for my $i (0..1) {
		for my $j (0..1) {
			$hash = $zp * $hash + index2d($M, $i,$j);				
		}
	}

	return $hash;
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
	print "Diameter: " . $graph->diameter. "\n";
	

	return $graph;
}

	# Probably not best way to test it
sub find_result
{
	my ($multiplication_results_ref, $node_to_find, $zp, $hash_table_size) = @_;

	my $hash_no = compute_hash($node_to_find, $zp);
	my $index_no = $hash_no % $hash_table_size;


	if(defined($multiplication_results_ref->[$index_no])) {
		foreach my $node ( @{ $multiplication_results_ref->[$index_no] } ) { 
				# There is such parent node on index
			if(all $node->[0] == $node_to_find) {
				return 1; 
			} 		
		}
			# No such node on index
		return 0;
	} else {
			# First node on index
		return 0;
	}

	print "There is something very wrong\n";
	exit;
}

sub insert_result
{
	my ($keys_ref, $multiplication_results_ref, $node_place, $node_to_insert, $zp, $hash_table_size ) = @_;

	my $hash_no = compute_hash($node_place, $zp);
	my $index_no = $hash_no % $hash_table_size;

		# First parent node on index
	if(not defined($multiplication_results_ref->[$index_no])) {
		push @{ $multiplication_results_ref->[$index_no] }, [ $node_place, $node_to_insert ];
	}

		# Child node 
	foreach my $node ( @{ $multiplication_results_ref->[$index_no] } ) { 
		if(all $node->[0] == $node_place) {
			push @{ $node }, $node_to_insert;
		} 	
	}

		# Putting node on last position on index 
	push @{ $multiplication_results_ref->[$index_no] }, [ $node_place, $node_to_insert ];
}

sub generate_group
{
	my ($generating_set_ref, $zp, $hash_table_size) = @_;
	my @generating_set = @{ $generating_set_ref };
	my @stack = @generating_set;
	my @multiplication_results;

	#####
	my @t0 = gettimeofday();
	#####

	my $current_node = $stack[0]; 
	my @keys = [ compute_hash($current_node, $zp), $current_node ];

	while(@stack) {
		foreach my $generating_element (@generating_set) {
			my $multiplication_result = ($current_node x $generating_element) % $zp;	
			insert_result( \@keys, \@multiplication_results, $current_node, $multiplication_result, $zp, $hash_table_size );
				# Possible performance improvment with checking @stack before putting in result
			push @stack, $multiplication_result;
		}

		shift @stack;

		while(@stack && find_result(\@multiplication_results, $stack[0], $zp, $hash_table_size)) {
			shift @stack;
		}

		if(@stack) {
			$current_node = $stack[0];
			push @keys, [ compute_hash($current_node, $zp), $current_node ];
		}
		#		print "Stack size : $#stack\n";

	}

	#####	
	print "Generovanie prvkov: " . tv_interval( \@t0 ) . " sekund\n";
	print "Size multiplication_results: " . format_bytes(total_size(\@multiplication_results)) . "\n";
	print "Number of nodes: " . ($#keys + 1) . "\n";
	print "############################################\n";
	#####

	return ( \@keys, \@multiplication_results );
}

sub get_index
{
	my ($A) = @_;

	return index2d($A, 0,0) . index2d($A, 0,1) . index2d($A, 1,0) . index2d($A, 1,1);
}

sub generate_GL_group 
{
	my ($zp) = @_;

	my @generating_set ;
	my $zpg = $zp - 1;

	foreach my $i (0..$zpg){
		foreach my $j (0..$zpg) {
			foreach my $k (0..$zpg) {
				foreach my $l (0..$zpg) {
					my $m = PDL::Matrix->pdl([[$i, $j],[$k, $l]]);
					if(determinant_Zp($m, $zp) != 0) {
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
		if(determinant_Zp($generating_element, $zp) == 0) {
			print "!!!!!!!!!!!!!! Null determinant !!!!!!!!!!!!\n";
			print $generating_element;
			print "\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n";
			exit;
		}
	}

	return \@generating_set;
}

sub compute_order_set
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
			print $res;
			<STDIN>;
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

#3497861;
#4256233;
#15485863;

my $zp = give_nth_prime(25);
my $hash_table_size = 154485863;


my @generating_set = 
	( 
		PDL::Matrix->pdl([[1,7],[7,3]]), 
		PDL::Matrix->pdl([[2,1],[1,3]]), 
	);

#compute_order_set(check_set(\@generating_set), $zp);

print "Order of GL(2,$zp): " . order_of_GL(2,$zp) . "\n";
print "Zp: $zp\n";
print "Hash table size: $hash_table_size\n";
print "############################################\n";

generate_group_alt(check_set(\@generating_set, $zp), $zp, $hash_table_size);
#make_graphical_output(generate_graph(generate_group(check_set(\@generating_set, $zp), $zp, $hash_table_size)));
#generate_graph(generate_group(check_set(\@generating_set, $zp), $zp));

sub make_matrix_label
{
	my ($A) = @_;

	return sprintf("%d", compute_hash($A, $zp));
}
