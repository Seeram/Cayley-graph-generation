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
# Consider getting rid of PDL 
# Use hash function for stack to avoid many 
# Consider using database instead of alocated data
# Consider paralelization in computing elements of group
#  - make performance tests for computing multiplication of matrices via perl structures
# Hash table size computing
#  - not really necessary
# Representing matrices only by its keys
# Consider making structured data for better readability
# Subroutine for reading primes instead of computing them

sub make_matrix_label
{
	my ($A, $zp) = @_;

	return sprintf("%d", compute_hash($A, $zp));
}

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

sub insert_hash
{
	my ($generating_nodes_ref, $node, $zp, $hash_table_size ) = @_;

	my $hash_no = compute_hash($node, $zp);

	unless(defined($generating_nodes_ref->{ $hash_no })) {
		$generating_nodes_ref->{ $hash_no } = $hash_no;

		return 1;
	}

	return 0;
}

sub find_hash
{
	my ($generating_nodes_ref, $node, $zp, $hash_table_size ) = @_;

	my $hash_no = compute_hash($node, $zp);
		
	if(defined($generating_nodes_ref->{ $hash_no })) {
		return 1;
	} else {
		return 0;
	}
}

sub generate_group
{
	my ($generating_set_ref, $zp, $hash_table_size) = @_;
	my @generating_set = @{ $generating_set_ref };
	my @stack = @generating_set;
	my %generating_nodes;
	my $graph = Graph::Undirected->new; 


	#####
	my @t0 = gettimeofday();
	#####

	my $current_node = $stack[0]; 
	insert_hash(\%generating_nodes, $current_node, $zp, $hash_table_size );
	my $counter = 1;


	while(@stack) {
		foreach my $generating_element (@generating_set) {
			my $multiplication_result = ($current_node x $generating_element) % $zp;	

			unless(find_hash(\%generating_nodes, $multiplication_result, $zp, $hash_table_size)) {
				push @stack, $multiplication_result;
			}

			unless(all $generating_element == $multiplication_result) {
				$graph->add_edge(make_matrix_label($current_node, $zp), make_matrix_label($multiplication_result, $zp));
			}
		}

		shift @stack;

		if(@stack) {
			$current_node = $stack[0];
			insert_hash(\%generating_nodes, $current_node, $zp, $hash_table_size );
		}
		

		$counter++;
		if(($counter % 10000) == 0) {
			print "Velkost grafu: " . format_bytes(total_size(\$graph)) . "\n";
			print "Pocet vrcholov: " . $graph->vertices . "\n";
			print "Pocet matic v stacku: " . $#stack . "\n";
			print "Velkost stacku: " . format_bytes(total_size(\@stack)) . "\n";
			print "############################################\n";
		}
	}

	#####
	#print "Generovanie prvkov: " . tv_interval( \@t0 ) . " sekund\n";
	#print "Pocet vrcholov: " . $graph->vertices . "\n";
	#	print "Velkost grafu: " . format_bytes(total_size(\$graph)) . "\n";
	#####
	
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

my $zp = give_nth_prime(7);
my $hash_table_size = 154485863;

my @generating_set = 
	(
		PDL::Matrix->pdl([[-1,0],[0,-1]]), 
		PDL::Matrix->pdl([[1,$a],[0,-1]]), 
		PDL::Matrix->pdl([[1,0],[$a,-1]]), 
		PDL::Matrix->pdl([[-1,0],[$a,1]]), 
		PDL::Matrix->pdl([[-1,$a],[0,1]]), 
	);

foreach my $z (2..10) {
	my $zp = give_nth_prime($z);
	print "zp: $zp\n";
	foreach my $a (6..$zp-1) {
		print "a: $a\n";
		my @generating_set = 
			(
				PDL::Matrix->pdl([[-1,0],[0,-1]]), 
				PDL::Matrix->pdl([[1,$a],[0,-1]]), 
				PDL::Matrix->pdl([[1,0],[$a,-1]]), 
				PDL::Matrix->pdl([[-1,0],[$a,1]]), 
				PDL::Matrix->pdl([[-1,$a],[0,1]]), 
			);
		print "Diameter: " .  generate_group(check_set(\@generating_set, $zp), $zp, $hash_table_size) . "\n";
		$z++;
	}
	print "Order of GL(2,$zp): " . order_of_GL(2,$zp) . "\n";
	print "######################################\n";
}
#print "Order of GL(2,$zp): " . order_of_GL(2,$zp) . "\n";
#print "Zp: $zp\n";
#print "Hash table size: $hash_table_size\n";
#print "############################################\n";


#compute_order_set(\@generating_set, $zp);
#generate_group(check_set(\@generating_set, $zp), $zp, $hash_table_size);
#generate_group(check_set(\@generating_set, $zp), $zp, $hash_table_size);
#generate_graph(generate_group(check_set(\@generating_set, $zp), $zp));
