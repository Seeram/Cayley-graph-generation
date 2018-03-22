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
# Consider paralelization in computing elements of group
#  - make performance tests for computing multiplication of matrices via perl structures
# Hash table size computing
#  - not really necessary

sub make_matrix_label
{
	my ($A, $zp) = @_;

	return sprintf("%d", compute_hash($A, $zp));
}

sub determinant_Zp 
{
	my ($M, $zp) = @_;

	my $det = index2d($M, 0,0) * index2d($M, 1,1) - index2d($M, 0,1) * index2d($M, 1,0);

	return modulo($det, $zp);
}

sub modulo 
{
	my ($n, $z) = @_;

	return ($n % $z + $z) % $z;
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

sub insert_result
{
	my ($multiplication_results_ref, $node_place, $node_to_insert, $zp, $hash_table_size ) = @_;

	my $hash_no = compute_hash($node_place, $zp);
	my $index_no = $hash_no % $hash_table_size;

		# First parent node on index
	if(not defined($multiplication_results_ref->[$index_no])) {
		push @{ $multiplication_results_ref->[$index_no] }, [ $node_place, $node_to_insert ];
		return;
	}

		# Child node 
	foreach my $node ( @{ $multiplication_results_ref->[$index_no] } ) { 
		if(all $node->[0] == $node_place) {
			push @{ $node }, $node_to_insert;
			return;
		} 	
	}

		# Putting node on last position on index 
	push @{ $multiplication_results_ref->[$index_no] }, [ $node_place, $node_to_insert ];

	return;
}

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

sub insert_hash
{
	my ($generating_nodes_ref, $node, $zp) = @_;

	my $hash_no = compute_hash($node, $zp);

	unless(defined($generating_nodes_ref->{ $hash_no })) {
		$generating_nodes_ref->{ $hash_no } = $hash_no;

		return 1;
	}

	return 0;
}

sub find_hash
{
	my ($generating_nodes_ref, $node, $zp) = @_;

	my $hash_no = compute_hash($node, $zp);
		
	if(defined($generating_nodes_ref->{ $hash_no })) {
		return 1;
	} else {
		return 0;
	}
}

sub generate_group
{
	print "Generation of group\n";
	my ($generating_set_ref, $zp, $hash_table_size) = @_;
	my @generating_set = @{ $generating_set_ref };
	my @stack = @generating_set;
	my @multiplication_results;
	my %generating_nodes;


	#####
	my @t0 = gettimeofday();
	#####

	my $current_node = $stack[0]; 
	my @keys;
	push @keys, compute_hash($current_node, $zp);

	while(@stack) {
		foreach my $generating_element (@generating_set) {
			my $multiplication_result = ($current_node x $generating_element) % $zp;	
			insert_result(\@multiplication_results, $current_node,  $multiplication_result, $zp, $hash_table_size);
			print find_hash(\%generating_nodes, $multiplication_result, $zp, $hash_table_size);
			unless(find_hash(\%generating_nodes, $multiplication_result, $zp, $hash_table_size)) {
				push @stack, $multiplication_result;
			}
		}

		shift @stack;

		if(@stack) {
			$current_node = $stack[0];
			insert_hash(\%generating_nodes, $current_node, $zp, $hash_table_size );
			push @keys, compute_hash($current_node, $zp);
		}
	}
	
	return ( \@keys, \@multiplication_results, $zp );
}

sub generate_graph_from_table
{
	print "Generating graph from table\n";
	#####
	my @t0 = gettimeofday();
	#####

	my ($keys_ref, $multiplication_results_ref, $zp) = @_;
	my $graph = Graph::Undirected->new; 

	print "Number of keys: " . $#{ $keys_ref } . "\n";
	foreach my $index ( @{ $keys_ref } ) {
		foreach my $table_entry_ref ( @{ $multiplication_results_ref->[$index] } ) {
			foreach my $edge ( @{ $table_entry_ref } ) {
				unless (all $edge == $table_entry_ref->[0]) {
					$graph->add_edge(make_matrix_label($table_entry_ref->[0], $zp), make_matrix_label($edge, $zp));
				}
			}
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

sub generate_graph
{
	my ($generating_set_ref, $zp, $hash_table_size) = @_;
	my @generating_set = @{ $generating_set_ref };
	my @stack = @generating_set;
	my %generating_nodes;
	my $graph = Graph::Undirected->new(); 


	#####
	my @t0 = gettimeofday();
	#####

	my $current_node = $stack[0]; 
	insert_hash(\%generating_nodes, $current_node, $zp, $hash_table_size );
	

	while(@stack) {
		foreach my $generating_element (@generating_set) {
			my $multiplication_result = ($current_node x $generating_element) % $zp;	
			unless(find_hash(\%generating_nodes, $multiplication_result, $zp)) {
				push @stack, $multiplication_result;
			}

			unless(all $generating_element == $multiplication_result) {
				$graph->add_edge(make_matrix_label($current_node, $zp), make_matrix_label($multiplication_result, $zp));
			}
		}

		shift @stack;

		if(@stack) {
			$current_node = $stack[0];
			insert_hash(\%generating_nodes, $current_node, $zp);
		}
	}

	#my $writer = Graph::Writer::Dot->new();
	#$writer->write_graph($graph, 'graph.dot');

	#	system "circo", "-Tsvg", "graf.dot", "-o", "outfile.svg";
	
	print "Number of vertices: " . $graph->vertices;
	<STDIN>;
	print "pocitam\n";
	return $graph->diameter;
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

sub generate_SL_group 
{
	my ($zp) = @_;

	my @generating_set ;
	my $zpg = $zp - 1;

	foreach my $i (0..$zpg){
		foreach my $j (0..$zpg) {
			foreach my $k (0..$zpg) {
				foreach my $l (0..$zpg) {
					my $m = PDL::Matrix->pdl([[$i, $j],[$k, $l]]);
					if(determinant_Zp($m, $zp) == 1) {
						push @generating_set, $m;
					}
				}
			}
		}
	}

	return \@generating_set;
}

sub generate_arbitrary_group 
{
	my ($zp) = @_;

	my @generating_set ;
	my $zpg = $zp - 1;

	foreach my $i (0..$zpg){
		foreach my $j (0..$zpg) {
			foreach my $k (0..$zpg) {
				my $m = PDL::Matrix->pdl([[$i, $j],[0, $k]]);
				if(determinant_Zp($m, $zp) != 0) {
					# print $m;
					# <STDIN>;
					push @generating_set, $m;
				}
			}
		}
	}

	return \@generating_set;
}

sub find_group_inverse
{
	my ($matrix, $zp) = @_;

	my $null_matrix = PDL::Matrix->pdl([[0, 0],[0, 0]]);
	my $one_matrix = PDL::Matrix->pdl([[1, 0],[0, 1]]);
	my $zpg = $zp - 1;

	foreach my $i (0..$zpg){
		foreach my $j (0..$zpg) {
			foreach my $k (0..$zpg) {
				foreach my $l (0..$zpg) {
					my $inverse = PDL::Matrix->pdl([[$i, $j],[$k, $l]]);
					if(any $inverse != $null_matrix) { 
						my $m = ($matrix x $inverse) % $zp;
						if(all $m == $one_matrix) {
							return $inverse;
						}
					}
				}
			}
		}
	}
}

sub check_GL_set
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

sub check_SL_set
{
	my ($generating_set_ref, $zp) = @_;
	my @generating_set = @{ $generating_set_ref };


	@generating_set = map { $_ % $zp } @generating_set;
	foreach my $generating_element (@generating_set) {
		if(determinant_Zp($generating_element, $zp) != 1) {
			print "!!!!!!!!!!!!!! Determinant not equal 1!!!!!!!!!!!!\n";
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
			#		print $res;
			#       <STDIN>;
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

	print "Making graphical output on" .  $graph->vertices . "vertices\n";

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

sub order_of_SL
{
	my ($n, $q) = @_;

	my $order = 1;
	foreach my $k (0..$n-1) {
		$order = $order * ($q**$n - $q**$k);
	}

	return ($order / ($q - 1));
}

my $zp = give_nth_prime(4);
print "Zp: $zp\n";
print "Order of GL(2,$zp): " . order_of_GL(2,$zp) . "\n";	
my $hash_table_size = 154485863;

my @generating_set = 
	(
		#				PDL::Matrix->pdl([[2,0],[1,3]]), 
				PDL::Matrix->pdl([[2,0],[1,2]]), 
				PDL::Matrix->pdl([[2,1],[1,1]]), 
				PDL::Matrix->pdl([[2,1],[1,0]]), 
				PDL::Matrix->pdl([[2,2],[1,0]]), 
	);

push @generating_set, find_group_inverse(PDL::Matrix->pdl([[2,0],[1,2]]), $zp); 
push @generating_set, find_group_inverse(PDL::Matrix->pdl([[2,1],[1,1]]), $zp);
push @generating_set, find_group_inverse(PDL::Matrix->pdl([[2,1],[1,0]]), $zp);
push @generating_set, find_group_inverse(PDL::Matrix->pdl([[2,2],[1,0]]), $zp);

generate_graph_from_table(generate_group(check_GL_set(\@generating_set, $zp), $zp, $hash_table_size));
