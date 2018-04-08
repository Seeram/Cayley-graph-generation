#!/usr/bin/perl

use strict;
use warnings;

use PDL;
use PDL::Matrix;
use PDL::NiceSlice;

use Graph::Directed;
use Graph::Writer::Dot;

use Data::Dumper;
use List::MoreUtils qw( );
use List::Util qw( );

use Devel::Size qw( size total_size );
use Number::Format qw( format_bytes );
use Time::HiRes qw( gettimeofday tv_interval);
use Parallel::ForkManager;

use Math::GMPz qw( Rmpz_get_ui );
use Math::Primality qw( next_prime );

use Algorithm::Combinatorics qw( combinations variations_with_repetition );

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
	#	my $index_no = $hash_no % $hash_table_size;
	my $index_no = $hash_no;

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

sub print_hash_table 
{
	print "Printing hash table\n";
	my ($generating_nodes_ref) = @_;

	my %ht = %{ $generating_nodes_ref };

	foreach my $key ( keys %ht ) {
		print "$key\n";
	}

	my @keys = keys %ht;

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

	if( defined $generating_nodes_ref->{ $hash_no } ) {
		return 0;
	} else {
		return 1;
	}
}

sub find_diameter
{
	my ($keys_ref, $multiplication_results_ref, $generation_set_ref, $zp) = @_;
	my @checked_diameters = qw(1 2 3 4 5 6 7 8 9 10 );

	foreach my $diameter ( @checked_diameters ) {
		if(check_diameter($keys_ref, $multiplication_results_ref, $generation_set_ref, $zp, $diameter)) {
			return $diameter;
		}
	}

	return undef;
}

sub check_diameter
{
	my ($keys_ref, $multiplication_results_ref, $generation_set_ref, $zp, $diameter) = @_;

	my @generation_set = @{ $generation_set_ref }; 
	my @hash_storage;

	if($diameter == 1) {
		foreach my $index_no ( @{ $keys_ref } ) {
			foreach my $table_entry_ref ( @{ $multiplication_results_ref->[$index_no] } ) {
				if( $#{ $keys_ref } != $#{ $table_entry_ref } ) {
					return 0;
				}
			}
		}
		return 1;
	}
			

	foreach my $i ( 2..$diameter ) {
		my $variations = variations_with_repetition([0...$#generation_set], $i);
		while (my $variation = $variations->next) {
			my $m = $generation_set[$variation->[0]];
			foreach my $j ( 1..($i-1) ) {
				$m = ($m x $generation_set[$variation->[$j]]) % $zp;
			}
			push @hash_storage, compute_hash($m, $zp);
		}
	}

	foreach my $m ( @{ $generation_set_ref } ) {
		push @hash_storage, compute_hash($m, $zp);
	}

	foreach my $key ( @{ $keys_ref } ) {
		return 0 unless(List::Util::any {$_ eq $key} @hash_storage);
	}

	return 1;
}

sub generate_group
{
	#####
	my @t0 = gettimeofday();
	#####
	
	my ($generating_set_ref, $zp, $hash_table_size) = @_;
	my @multiplication_results;
	my %generating_nodes;
	
	my @generating_set = @{ $generating_set_ref };
	my @keys;
	my @stack;

	foreach my $gs_element ( @generating_set ) {
		insert_hash(\%generating_nodes, $gs_element, $zp, $hash_table_size );
		push @keys, compute_hash($gs_element, $zp);
		push @stack, $gs_element;
	}

	my $current_node = $stack[0]; 

	while(@stack) {
		foreach my $generating_element (@generating_set) {
			my $multiplication_result = ($current_node x $generating_element) % $zp;	
			insert_result(\@multiplication_results, $current_node,  $multiplication_result, $zp, $hash_table_size);
			if(find_hash(\%generating_nodes, $multiplication_result, $zp)) {
				insert_hash(\%generating_nodes, $multiplication_result, $zp, $hash_table_size );
				push @keys, compute_hash($multiplication_result, $zp);
				push @stack, $multiplication_result;
			}
		}

		shift @stack;

		if(@stack) {
			$current_node = $stack[0];
		}
	}

	return ( \@keys, \@multiplication_results, $generating_set_ref, $zp);
}

sub generate_graph_from_table
{
	my ($keys_ref, $multiplication_results_ref, $generating_set_ref, $zp) = @_;
	my $graph = Graph::Undirected->new; 

	#print "Number of keys: " . $#{ $keys_ref } . "\n";
	foreach my $index ( @{ $keys_ref } ) {
		foreach my $table_entry_ref ( @{ $multiplication_results_ref->[$index] } ) {
			foreach my $edge ( @{ $table_entry_ref } ) {
				unless (all $edge == $table_entry_ref->[0]) {
					$graph->add_edge(make_matrix_label($table_entry_ref->[0], $zp), make_matrix_label($edge, $zp));
				}
			}
		}
	}

	my $diameter = $graph->diameter;

	return ( $graph, $generating_set_ref, $zp, $diameter );
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
	my $neutral_element = PDL::Matrix->pdl([[1, 0],[0, 1]]);

	foreach my $i (0..$zpg){
		foreach my $j (0..$zpg) {
			foreach my $k (0..$zpg) {
				foreach my $l (0..$zpg) {
					my $m = PDL::Matrix->pdl([[$i, $j],[$k, $l]]);
					if(determinant_Zp($m, $zp) == 1) {
						unless(all $m == $neutral_element) {
							push @generating_set, $m;
						}
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
	my ($graph, $generating_set_ref, $zp, $diameter, $filename) = @_;

	my $writer = Graph::Writer::Dot->new();
	$writer->write_graph($graph, 'graf.dot');
	my $folder = "graphs/";

	my $hash = "";
	foreach my $mat ( @{ $generating_set_ref } ) {
		$hash = $hash . compute_hash($mat, $zp) . ".";
	}

	if( not defined  $filename ) {
		$filename = "GeneratingSetSize_" . ($#{ $generating_set_ref } + 1) . "_Diameter_" . $diameter . "_Zp_" . $zp . "_$hash";

		open(my $file, ">", $folder . $filename . "gs")
			or die "cannot open > " . $folder .  $filename . "gs" . ": $!";

		print $file "Group: SL(2,$zp)\n";
		print $file "Diameter of Cayley graph: $diameter\n";
		print $file "Generating set:\n";

		foreach my $matrix ( @{ $generating_set_ref } ) {
			print $file $matrix;
		}

		close $file;
	} 

	system "circo", "-Tsvg", "graf.dot", "-o", $folder . $filename . ".svg";
}

sub make_group_output
{
	my ($keys_ref, $multiplication_results_ref, $generating_set_ref, $zp, $diameter, $filename) = @_;

	my $folder = "graphs/";
	my $hash = "";
	foreach my $mat ( @{ $generating_set_ref } ) {
		$hash = $hash . compute_hash($mat, $zp) . ".";
	}

	if( not defined  $filename ) {
		$filename = "GeneratingSetSize_" . ($#{ $generating_set_ref } + 1) . "_Diameter_" . $diameter . "_Zp_" . $zp . "_$hash";
	} 

	open(my $file, ">", $folder . $filename . "gs")
		or die "cannot open > " . $folder .  $filename . "gs" . ": $!";

	print $file "Group: SL(2,$zp)\n";
	print $file "Diameter of Cayley graph: $diameter\n";
	print $file "Generating set size: $#{ $generating_set_ref }\n";
	print $file "Generating set:\n";

	foreach my $matrix ( @{ $generating_set_ref } ) {
		print $file $matrix;
	}

	close $file;
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

sub generate_all_degree_diameter_solution_graphs
{
	my $zp = give_nth_prime(2);
	my @group = @{ generate_SL_group($zp) };
	my $hash_table_size = 154485863;

	print "Zp: $zp\n";
	print "Order of SL(2,$zp): " . order_of_SL(2,$zp) . "\n";	

	my $moor_boundary = int(sqrt($#group)) + 1;
	foreach my $num_of_elements ( (($moor_boundary/2))..($#group) ) {
		my $combinations = combinations([0..$#group], $num_of_elements);
		while(my $combination = $combinations->next) {
			my @chosen_set;

			foreach my $group_index ( @{ $combination } ) {
				push @chosen_set, $group[$group_index];
				push @chosen_set, find_group_inverse($group[$group_index], $zp);
			}
			
				# Remove same matrices if in chosen set was inverse of some other element
			my @generating_set = List::MoreUtils::uniq @chosen_set;
				#Change according to new arguments
			#make_graphical_output(generate_graph_from_table(generate_group(check_GL_set(\@generating_set, $zp), $zp, $hash_table_size)));
		}
	}
}

sub generate_degree_diameter_solution
{
	####
	my @t0 = gettimeofday();
	####
	
	my $zp = give_nth_prime(3);
	my @group = @{ generate_SL_group($zp) };
	my $hash_table_size = 154485863;
	my $pm = new Parallel::ForkManager( 0 );

	print "Zp: $zp\n";
	print "Order of SL(2,$zp): " . order_of_SL(2,$zp) . "\n";	

	my $moor_bound = int(sqrt($#group)) + 1;
	foreach my $num_of_elements ( (($moor_bound/2))..($#group + 1) ) {
		my $combinations = combinations([0..$#group], $num_of_elements);
		my $counter = 0;
		while(my $combination = $combinations->next) {
			$counter++;
			if($counter == 15) {
				exit;
			}
			srand time;
			$pm->start and next;
			my @chosen_set;
			foreach my $group_index ( @{ $combination } ) {
				push @chosen_set, $group[$group_index];
				push @chosen_set, find_group_inverse($group[$group_index], $zp);
			}
				# Remove same matrices if in chosen set was inverse of some other element
			my @generating_set = List::MoreUtils::uniq @chosen_set;
			my @group = generate_group(check_GL_set(\@generating_set, $zp), $zp, $hash_table_size);
			my $diameter = find_diameter(@group);
			print join(", ", @{ $combination }) . "\t\t\t\t\t\t\t\tDiameter: $diameter\n";
			make_group_output(@group, $diameter);
			$pm->finish;
		}
	}
}

generate_degree_diameter_solution();
