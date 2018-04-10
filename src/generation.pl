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

my @multiplication_inverse_finite_field;
my @multiplication_finite_field;
my @addition_inverse_finite_field;

sub fill_finite_field_arithmetic_tables
{
	my ($zp) = @_;

	foreach my $i ( 1..($zp - 1) ) {
		foreach my $j ( 1..($zp - 1) ) {
			if(modulo($i * $j, $zp) == 1) {
				$multiplication_inverse_finite_field[$i] = $j;
			}
		}
	}

	foreach my $i ( 0..($zp - 1) ) {
		foreach my $j ( 0..($zp - 1) ) {
			$multiplication_finite_field[$i][$j] = modulo($i * $j, $zp);
		}
	}

	foreach my $i ( 0..($zp - 1) ) {
		foreach my $j ( 0..($zp - 1) ) {
			if(modulo($i + $j, $zp) == 0) {
				$addition_inverse_finite_field[$i] = $j;
			}
		}
	}
}

sub make_matrix_label
{
	my ($A, $zp) = @_;

	return sprintf("%d", compute_hash($A, $zp));
}

sub determinant_Zp 
{
	my ($m, $zp) = @_;

	my $det = index2d($m, 0,0) * index2d($m, 1,1) - index2d($m, 0,1) * index2d($m, 1,0);

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
	my @checked_diameters = 1..10;

	foreach my $diameter ( @checked_diameters ) {
		if(check_one_diameter($keys_ref, $multiplication_results_ref, $generation_set_ref, $zp, $diameter)) {
			return $diameter;
		}
	}

	return undef;
}

sub check_diameter
{
	my ($keys_ref, $multiplication_results_ref, $generation_set_ref, $zp, $diameter) = @_;

	if($diameter == 1) {
		return check_one_diameter($keys_ref, $multiplication_results_ref, $generation_set_ref, $zp, $diameter);
	} 	

	if(check_one_diameter($keys_ref, $multiplication_results_ref, $generation_set_ref, $zp, $diameter)) {
	  if(!check_one_diameter($keys_ref, $multiplication_results_ref, $generation_set_ref, $zp, $diameter - 1)) {
		  return 1;
	  } else {
		  return 0;
	  }
	} else {
		return 0;
	}
}

	# Check one diameter of graph, note graphs with diameter d are also with diameter (d + 1)  
sub check_one_diameter
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

sub generate_cayley_graph
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
	my ($m, $zp) = @_;
	my $det_inverse = $multiplication_inverse_finite_field[determinant_Zp($m, $zp)];

	my $eye_matrix = PDL::Matrix->pdl([[1, 0],[0, 1]]);

	my $a = $multiplication_finite_field[index2d($m, 1,1)][$det_inverse];
	my $b = $multiplication_finite_field[$addition_inverse_finite_field[index2d($m, 1,0)]][$det_inverse];
	my $c = $multiplication_finite_field[$addition_inverse_finite_field[index2d($m, 0,1)]][$det_inverse];
	my $d = $multiplication_finite_field[index2d($m, 0,0)][$det_inverse];

	return PDL::Matrix->pdl(
								[
							   		[ $a, $c ],
									[ $b, $d ] 
							   	]
							  );
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

sub find_involutions
{
	my ($group_ref, $zp) = @_;

	my $eye = PDL::Matrix->pdl([[1,0],[0,1]]);
	my @indeces_of_involutions;

	foreach my $i ( 0..$#{ $group_ref } ) {
		my $m = ($group_ref->[$i] x $group_ref->[$i]) % $zp;
		if(all $m == $eye) {
			push @indeces_of_involutions, $i;
		}
	}

	return \@indeces_of_involutions;
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

sub save_generating_set_and_diameter
{
	my ($keys_ref, $multiplication_results_ref, $generating_set_ref, $zp, $diameter, $folder, $filename) = @_;

	my $hash = "";
	foreach my $mat ( @{ $generating_set_ref } ) {
		$hash = $hash . compute_hash($mat, $zp) . ".";
	}

	if( not defined  $folder ) {
		$folder = "results/";
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

sub get_nth_prime 
{
	my ($n) = @_;

	my $prime = 2;
	foreach my $i (2..$n) {
		$prime = next_prime($prime);
	}

	return Rmpz_get_ui $prime;
}

sub get_order_of_GL
{
	my ($n, $q) = @_;

	my $order = 1;
	foreach my $k (0..$n-1) {
		$order = $order * ($q**$n - $q**$k);
	}

	return $order;
}

sub get_order_of_SL
{
	my ($n, $q) = @_;

	my $order = 1;
	foreach my $k (0..$n-1) {
		$order = $order * ($q**$n - $q**$k);
	}

	return ($order / ($q - 1));
}

sub get_moore_bound
{
	my ($degree, $diameter) = @_;

	if($diameter == 2) {
		return 2 * $diameter + 1;
	} else {
		return 1 + $degree * ((($degree - 1)**$diameter - 1) / ($degree - 2));
	}
}

sub get_random_generating_set 
{
	my ($group_ref, $zp, $number_of_elements, $number_of_forks, $hash_table_size) = @_;
}

sub get_incremenet_generating_set
{
	my ($group_ref, $zp, $combinations_ref, $required_size_of_set) = @_;
	my @generating_set;
	my $combination;

	while($required_size_of_set != ($#generating_set + 1)) {
		my @set;
		$combination = ${ $combinations_ref }->next;

		foreach my $chosen_element ( @{ $combination } ) {
			push @set, $group_ref->[0]->[$chosen_element];
			push @set, find_group_inverse($group_ref->[0]->[$chosen_element], $zp);
		}

		@generating_set = List::MoreUtils::uniq @set;
	}

	print join(", ", @{ $combination }) . "\n";

	return \@generating_set;
}

sub generate_sets_incrementally
{
	my ($group_ref, $zp, $degree, $number_of_forks, $hash_table_size) = @_;

	my $pm = new Parallel::ForkManager( $number_of_forks );
	my $combinations = combinations([0..$#{ $group_ref->[0] }], $degree/2);
	my $counter = 1;

	while(my $combination = $combinations->next) {
		print "[$counter] "; $counter++;
		my @generating_set = @{ get_incremenet_generating_set($group_ref, $zp, \$combinations, $degree -1) };

		$pm->start and next;
			my @cayley_graph = generate_cayley_graph(\@generating_set, $zp, $hash_table_size);

			if(check_diameter(@cayley_graph, 2)) {
				my @graph = generate_graph_from_table(@cayley_graph);
				if($graph[$#graph] == 2) {
					save_generating_set_and_diameter(@cayley_graph, 2, "results/");
				} else {
					save_generating_set_and_diameter(@cayley_graph, 2, "wrong_computed_diameter/");
				}
			} 		
		$pm->finish;
	}
}

my $hash_table_size = 154485863;
my $diameter = 2;
my $number_of_forks = 4;
my @group;
my $zp = get_nth_prime(3);
print "Zp: $zp\n";
print "Order of SL(2,$zp): " . get_order_of_SL(2,$zp) . "\n";	

print "Filling up arithmetic tables of finite field: ";
fill_finite_field_arithmetic_tables($zp);
print "\t\t\t\t\t\t[OK]\n";
print "Generating group elements: ";
push @group, generate_SL_group($zp);
print "\t\t\t\t\t\t\t\t[OK]\n";
print "Looking for involutions: ";
push @group, find_involutions($group[0], $zp);
print "\t\t\t\t\t\t\t\t[OK]\n";
print "####################################################################################################################################\n";

#my $moore_degree_for_diameter_two = int(sqrt($#{ $group[0] }));
my $moore_degree_for_diameter_two = 10;

generate_sets_incrementally(\@group, $zp, $moore_degree_for_diameter_two, $number_of_forks, $hash_table_size);
