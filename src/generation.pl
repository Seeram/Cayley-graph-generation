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
use Digest::MD5 qw( md5 );

use Devel::Size qw( size total_size );
use Number::Format qw( format_bytes );
use Time::HiRes qw( gettimeofday tv_interval);
use Parallel::ForkManager;

use Math::GMPz qw( Rmpz_get_ui );
use Math::Primality qw( next_prime );

use Algorithm::Combinatorics qw( combinations variations_with_repetition variations );

my @multiplication_inverse_finite_field;
my @multiplication_finite_field;
my @addition_inverse_finite_field;
my @global_time = gettimeofday();

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

	my $hash = 0;
	for my $i (0..1) {
		for my $j (0..1) {
			$hash = $zp * $hash + index2d($A, $i,$j);				
		}
	}

	return sprintf("%d", $hash);
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
	my ($A, $zp) = @_;

	my $hash = 0;
	for my $i (0..1) {
		for my $j (0..1) {
			$hash = $zp * $hash + index2d($A, $i,$j);				
		}
	}

	return $hash;
}

sub insert_result
{
	my ($multiplication_results_ref, $node_place, $node_to_insert, $zp ) = @_;

	my $hash_no = compute_hash($node_place, $zp);
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
	my ($multiplication_results_ref, $node_to_find, $zp ) = @_;

	my $hash_no = compute_hash($node_to_find, $zp);
	my $index_no = $hash_no;


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
	my ($generation_set_ref, $zp) = @_;
	my @checked_diameters = 1..10;

	foreach my $diameter ( @checked_diameters ) {
		if(check_one_diameter($generation_set_ref, $zp, $diameter)) {
			return $diameter;
		}
	}

	print "Undefined\n";
	return undef;
}

sub check_diameter
{
	my ($generation_set_ref, $zp, $diameter) = @_;

	if($diameter == 1) {
		return check_one_diameter($generation_set_ref, $zp, $diameter);
	} 	

	if(check_one_diameter($generation_set_ref, $zp, $diameter)) {
	  if(!check_one_diameter($generation_set_ref, $zp, $diameter - 1)) {
		  return 1;
	  } else {
		  return 0;
	  }
	} else {
		return 0;
	}
}

	# Check one diameter of graph, warning graphs with diameter d are also with diameter (d + 1)  
sub check_one_diameter
{
	my ($generation_set_ref, $zp, $diameter) = @_;

	my @generation_set = @{ $generation_set_ref }; 
	my @hash_storage;

	if($diameter == 1) {
		my @cayley_graph = generate_cayley_graph( $generation_set_ref, $zp );

		foreach my $index_no ( @{ $cayley_graph[0] } ) {
			foreach my $table_entry_ref ( @{ $cayley_graph[1]->[$index_no] } ) {
				if($#{ $cayley_graph[0] } != $#{ $table_entry_ref } ) { 
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

	@hash_storage = List::MoreUtils::uniq @hash_storage;

	if(($#hash_storage + 1) == get_order_of_SL(2,$zp)) {
		return 1;	
	} else {
		return 0;
 	}	
}

sub check_one_girth
{
	my ($generation_set_ref, $zp, $girth) = @_;

	if($girth < 3) {
		print "Wrong girth in check one girth";
		exit;
	}

	my $eye = PDL::Matrix->pdl([[1,0],[0,1]]);

	my @generation_set = @{ $generation_set_ref }; 

	my $variations = variations_with_repetition([0...$#generation_set], $girth);
	while (my $variation = $variations->next) {
		my $m = $generation_set[$variation->[0]];
		foreach my $j ( 1..($girth-1) ) {
			$m = ($m x $generation_set[$variation->[$j]]) % $zp;
		}
		if(all $m == $eye) {
			return 1;	
		}
	}

	return 0;

}

sub check_girth
{
	my ($generation_set_ref, $zp, $girth) = @_;

	if($girth < 3) {
		print "Wrong girth in check one girth";
		exit;
	}

	if(check_one_girth($generation_set_ref, $zp, $girth)) {
		foreach my $i ( 3..($girth - 1)) {
			if(check_one_girth($generation_set_ref, $zp, $i)) {
				return 0;	
			}
		}
		return $girth;
	} else {
		return 0;
	}
}

sub generate_cayley_graph
{
	my ( $generating_set_ref, $zp ) = @_;
	my @multiplication_results;
	my %generating_nodes;
	
	my @generating_set = @{ $generating_set_ref };
	my @keys;
	my @stack;

	foreach my $gs_element ( @generating_set ) {
		insert_hash(\%generating_nodes, $gs_element, $zp);
		push @keys, compute_hash($gs_element, $zp);
		push @stack, $gs_element;
	}

	my $current_node = $stack[0]; 

	while(@stack) {
		foreach my $generating_element (@generating_set) {
			my $multiplication_result = ($current_node x $generating_element) % $zp;	
			insert_result(\@multiplication_results, $current_node,  $multiplication_result, $zp);
			if(find_hash(\%generating_nodes, $multiplication_result, $zp)) {
				insert_hash(\%generating_nodes, $multiplication_result, $zp);
				push @keys, compute_hash($multiplication_result, $zp);
				push @stack, $multiplication_result;
			}
		}

		shift @stack;

		if(@stack) {
			$current_node = $stack[0];
		}
	}

	return ( \@keys, \@multiplication_results, $generating_set_ref, $zp );
}

sub generate_graph_from_cayley_graph
{
	my ($keys_ref, $multiplication_results_ref, $generating_set_ref, $zp) = @_;
	my $graph = Graph::Undirected->new; 

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
	my ($A, $zp) = @_;

	if($zp < 99) {
		return index2d($A, 0,0) . index2d($A, 0,1) . index2d($A, 1,0) . index2d($A, 1,1);
	} else {
		my $hash = 0;
		for my $i (0..1) {
			for my $j (0..1) {
				$hash = $zp * $hash + index2d($A, $i,$j);				
			}
		}

		return $hash;
	}

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
		if(!(all $group_ref->[$i] == $eye)) {
			my $m = ($group_ref->[$i] x $group_ref->[$i]) % $zp;
			if(all $m == $eye) {
				push @indeces_of_involutions, $i;
			}
		}
	}

	return \@indeces_of_involutions;
}

sub compute_order_set
{
	my ($generating_set_ref, $zp) = @_;

	my $eye = PDL::Matrix->pdl([[1,0],[0,1]]);
	my $order_max = 0;
	my @orders;
	my @orders_and_max;

	foreach my $i ( 0..$#{ $generating_set_ref} ) {
		my $order = 1;
		my $res = $generating_set_ref->[$i];
		while(any $res != $eye) {
			$res = ($res x $generating_set_ref->[$i]) % $zp;
			$order++;
		}

		if($order > $order_max) {
			$order_max = $order;
		}
		push @orders, $order;
	}

	push @orders_and_max, \@orders;
	push @orders_and_max, $order_max;

	return \@orders_and_max;
}

sub make_graphical_output
{
	my ($graph, $generating_set_ref, $zp, $filename) = @_;

	my $writer = Graph::Writer::Dot->new();
	$writer->write_graph($graph, 'graf.dot');
	my $folder = "graphs/";

	my $hash = "";
	foreach my $mat ( @{ $generating_set_ref } ) {
		$hash = $hash . compute_hash($mat, $zp) . ".";
	}

	if( not defined  $filename ) {
		$filename = "GeneratingSetSize_" . ($#{ $generating_set_ref } + 1) . "_Zp_" . $zp . "_$hash";

		open(my $file, ">", $folder . $filename . "gs")
			or die "cannot open > " . $folder .  $filename . "gs" . ": $!";

		print $file "Group: SL(2,$zp)\n";
		print $file "Generating set:\n";

		foreach my $matrix ( @{ $generating_set_ref } ) {
			print $file $matrix;
		}

		close $file;
	} 

	system "circo", "-Tsvg", "graf.dot", "-o", $folder . $filename . ".svg";
}

sub save_cayley_graph
{
	my ($generating_set_ref, $zp, $diameter, $folder, $filename) = @_;

	my $postfix = int(rand(10000000000));

	if( not defined  $folder ) {
		$folder = "results/";
	}

	if( not defined  $filename ) {
		$filename = "GeneratingSetSize_" . ($#{ $generating_set_ref } + 1) . "_Diameter_" . $diameter . "_OrderOfGraph_" . get_order_of_SL(2, $zp) . "_Zp_" . $zp . "_" . $postfix;
	} 

	open(my $file, ">", $folder . $filename . ".gs")
		or die "cannot open > " . $folder .  $filename . ".gs" . ": $!";

	print $file "Group: SL(2,$zp)\n";
	print $file "Diameter of Cayley graph: $diameter\n";
	print $file "Generating set size: " . ($#{ $generating_set_ref } + 1) . "\n";
	print $file "Order of graph: " . get_order_of_SL(2,$zp) . "\n";
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

sub get_random_index 
{

	my ($group_ref) = @_;

	my $neutral_element = $group_ref->[2];

	while(1) {
		my $chosen_index = int(rand($#{ $group_ref->[0] } + 1 ));
		if($chosen_index != $neutral_element) {
			my $chosen_index_order = $group_ref->[3]->[0]->[$chosen_index];
			my $order_max = $group_ref->[3]->[1];
			my $rand = rand();

			if($rand < (($chosen_index_order / $order_max) * 0.8 )) {
				return $chosen_index;

			}
		}
	}
}

sub get_random_generating_set 
{
	my ($group_ref, $zp, $required_size_of_set) = @_;
	my @generating_set;
	my $chosen_index;

	while(($#generating_set + 1) < $required_size_of_set) {
			# get last element it has to be involution
		if(($#generating_set + 1) == ($required_size_of_set - 1)) {
				# Try just number of involutions in group to add random one 
			foreach ( 0..$#{ $group_ref->[1] } ) {
				$chosen_index = int(rand($#{ $group_ref->[1] } + 1 ));

				my $involution = $group_ref->[0]->[$group_ref->[1]->[$chosen_index]];
				unless(List::Util::any { all $_ == $involution } @generating_set) {
					push @generating_set, $involution;
					return \@generating_set;
				}
			}

				# Then try any of them
			foreach my $chosen_index ( @{ $group_ref->[1] } ) {
				my $involution = $group_ref->[0]->[$chosen_index];
				unless(List::Util::any {all $_ == $involution} @generating_set) {
					push @generating_set, $involution;
					return \@generating_set;
				}
			}
				# Hopeless try new combination
			return get_random_generating_set($group_ref, $zp, $required_size_of_set);
		}

		$chosen_index = get_random_index($group_ref);
		#while(($chosen_index = int(rand($#{ $group_ref->[0] } + 1 ))) == $group_ref->[2]) {};

		my $chosen_matrix = $group_ref->[0]->[$chosen_index];
		push @generating_set, $chosen_matrix;

			# Unless I have choosed index with involution add inverse
		unless(List::Util::any {$_ eq $chosen_index} @{ $group_ref->[1] }) {
			push @generating_set, find_group_inverse($chosen_matrix, $zp); 
		}

		@generating_set = List::MoreUtils::uniq @generating_set;
	}

	return \@generating_set;
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
			if($chosen_element != $group_ref->[2]) {
				push @set, $group_ref->[0]->[$chosen_element];
				push @set, find_group_inverse($group_ref->[0]->[$chosen_element], $zp);
			}
		}

		@generating_set = List::MoreUtils::uniq @set;
	}

	print join(", ", @{ $combination }) . "\n";

	return \@generating_set;
}

sub generate_sets_incrementally
{
	my ($group_ref, $zp, $size_of_generating_set, $number_of_forks, $hash_table_size) = @_;

	my $pm = new Parallel::ForkManager( $number_of_forks );
	my $combinations = combinations([0..$#{ $group_ref->[0] }], $size_of_generating_set/2);
	my $counter = 1;

	while(my $combination = $combinations->next) {
		print "[$counter] "; $counter++;
		my @generating_set = @{ get_incremenet_generating_set($group_ref, $zp, \$combinations, $size_of_generating_set) };

		$pm->start and next;
		#		my @cayley_graph = generate_cayley_graph(\@generating_set, $zp, $hash_table_size);
		#
		#	if(check_diameter(@cayley_graph, 2)) {
		#		my @graph = generate_graph_from_cayley_graph(@cayley_graph);
		#		if($graph[$#graph] == 2) {
		#			save_cayley_graph(@cayley_graph, 2, "results/");
		#		} else {
		#			save_cayley_graph(@cayley_graph, 2, "diameter_error/");
		#		}
		#	} 		
		$pm->finish;
	}
}

sub generate_sets_randomly
{
	my ($group_ref, $zp, $size_of_generating_set, $number_of_forks, $hash_table_size, $number_of_graphs) = @_;

	my $pm = new Parallel::ForkManager( $number_of_forks );

	my $counter = 1;

	while($counter <= $number_of_graphs) {

		my $generating_set_ref = get_random_generating_set($group_ref, $zp, $size_of_generating_set);

		$pm->start and next;
		#			my @t0 = gettimeofday();
		#	print "[$counter]\n"; $counter++;
		#	my @cayley_graph = generate_cayley_graph($generating_set_ref, $zp, $hash_table_size);
		#	my @graph = generate_graph_from_cayley_graph(@cayley_graph);
		#	if($graph[$#graph] != find_diameter(@cayley_graph)) {
		#		print "PROBLEM\n";
		#		print "graf diameter: $graph[$#graph]\n";
		#		print "cayley diameter: ". find_diameter(@cayley_graph) . "\n";;
		#		exit;
		#		} 		
		$pm->finish;
	}
}
sub	generate_cayley_graph_with_girth 
{
	my ($generating_set_ref, $zp, $hash_table_size, $size_of_generating_set, $girth) = @_;

	if(check_girth($generating_set_ref, $zp, $girth)) {
		if(check_symmetric_set($generating_set_ref, $zp, $size_of_generating_set)) {
			save_cayley_graph($generating_set_ref, $girth, "results/girth/");
			return $girth;
		} else {
			print "!!!!!!!!!!!!!!!! SET ERROR !!!!!!!!!!!!!!!!!!!!!!!\n";
			save_cayley_graph($generating_set_ref, $girth, "set_error/");
			return 0;
		}
	} else {
		return 0;
	}

	return 0;
}

sub	generate_cayley_graph_with_diameter 
{
	my ($generating_set_ref, $zp, $hash_table_size, $size_of_generating_set, $diameter, $check_diameter) = @_;

	if($check_diameter) {
			my @cayley_graph = generate_cayley_graph($generating_set_ref, $zp, $hash_table_size);
			my @graph = generate_graph_from_cayley_graph(@cayley_graph);
			my $found_diameter = find_diameter($generating_set_ref, $zp);
			my $graph_diameter = $graph[$#graph];
			if($graph_diameter != $found_diameter) {
				print "!!!!!!!!!!!!!!!! DIAMETER ERROR !!!!!!!!!!!!!!!!!!!!!!!\n";
				save_cayley_graph($generating_set_ref, $diameter, "diameter_error/");
			} else {
				print "\t\t[Diameter check] $graph[$#graph] == $found_diameter\n";
			}
	}

	if(check_diameter($generating_set_ref, $zp, $diameter)) {
		if(check_symmetric_set($generating_set_ref, $zp, $size_of_generating_set)) {
			save_cayley_graph($generating_set_ref, $diameter, "results/");
			return $diameter;
		} else {
			print "!!!!!!!!!!!!!!!! SET ERROR !!!!!!!!!!!!!!!!!!!!!!!\n";
			save_cayley_graph($generating_set_ref, $diameter, "set_error/");
			return 0;
		}
	} else {
		return 0;
	}

	return 0;
}


sub check_random_graphs
{
	my ($group_ref, $zp, $size_of_generating_set, $number_of_forks, $hash_table_size, $number_of_graphs, $time_limit, $diameter) = @_;

	my $counter = 0;
	my $pm = new Parallel::ForkManager( $number_of_forks );
	my @time;
	my $graph_found = 0;

	$pm->run_on_finish(
		sub
		{
			my ($pid, $exit_code, $ident) = @_;
			
			if($ident == 1) {
				my $graphs_in_time_limit = int(($time_limit / ($exit_code + 0.00000001 / $number_of_forks)))  - $number_of_forks;
				if($number_of_graphs > $graphs_in_time_limit) {
					print "\t\t\tAdjusting number of generated graphs on d=$size_of_generating_set to $graphs_in_time_limit to get it under time limit: $time_limit sec\n";
					$number_of_graphs = $graphs_in_time_limit;
				}
				return;

			}
			if($exit_code) {
				$graph_found = 1;
			}
		}
	);

	$pm->run_on_start(
		sub 
		{
			my ($pid, $ident) = @_; 
			print "[" . sprintf("%5.2lf", tv_interval(\@global_time)) . "][$ident/$number_of_graphs] generating graph on SL(2,$zp) with d=$size_of_generating_set\n";
		}
	);

	while($counter < $number_of_graphs) {
		$counter++;

		if($graph_found) {
			return 1;
		}


		my $generating_set_ref = get_random_generating_set($group_ref, $zp, $size_of_generating_set);

		$pm->start("$counter") and next;
			@time = gettimeofday();
			my $exit_code = generate_cayley_graph_with_diameter($generating_set_ref, $zp, $hash_table_size, $size_of_generating_set, $diameter, my $check_diameter_on_graph = 0);
			print "\t[" . sprintf("%5.2lf", tv_interval(\@global_time)) . "][$counter] finished in " . tv_interval(\@time) . " sec with exit code: $exit_code\n";
			if($counter == 1) {
				$pm->finish(tv_interval(\@time));
			}	
		$pm->finish($exit_code);

	}

	$pm->wait_all_children;
	if($graph_found) {
		return 1;
	} else {
		return 0;
	}
}

sub check_symmetric_set
{
	my ($generating_set_ref, $zp, $size) = @_;
	my @checked_matrices;	
	my $eye = PDL::Matrix->pdl([[1,0],[0,1]]);
	my $set_size = $#{ $generating_set_ref };

	if(($set_size + 1) != $size) {
		print "\tSet size error\n";
		return 0;
	} 		

	foreach my $m ( @{ $generating_set_ref } ) {
		if(all $m == $eye) {
			print "\tNeutral element in set\n";
			foreach my $n ( @{ $generating_set_ref } ) {
				print $n;
			}
			return 0;
		}
	}

	foreach my $i ( 1..$set_size ) {
		unless(List::Util::any {$_ eq $i} @checked_matrices) {
			push @checked_matrices, $i;
			my $m = $generating_set_ref->[$i];
			my $m_squared = ($m x $m) % $zp;
			unless(all $m_squared == $eye) {
				my $flag = 0;
				foreach my $j ( 0..$#{ $generating_set_ref } ) {
					my $res = ( $generating_set_ref->[$j] x $m ) % $zp;
					if(all $res == $eye) {
						push @checked_matrices, $j;
						$flag = 1;
					}
				}
				unless($flag) {
					print "\tInverse element not found\n";
					return 0;
				} 
			} 		
		}
	}

	my @generating_set = List::MoreUtils::uniq @{ $generating_set_ref };
	if($#generating_set != $#{ $generating_set_ref }) {
		print "\tUniq made generation set smaller!\n";
		return 0;
	}

	return 1;
}

sub fill_cayley_table
{
	my ($group_ref, $zp) = @_;

	my $group_size = $#{ $group_ref->[0] };
	my @cayley_table;

	foreach my $i ( 0..$group_size ) {
		foreach my $j ( 0..$group_size ) {
			print "[$i][$j]\n";
			my $res = $group_ref->[0]->[$i] x $group_ref->[0]->[$j] % $zp;

			my $k = 0;
			while(any $res != $group_ref->[0]->[$k]) { $k++ };
			$cayley_table[$i][$j] = $k;
		}
	}

	open(my $file, ">", "../cayley_tables/SL(2,$zp)" . ".ct")
		or die "cannot open > ../cayley_tablesSL(2,$zp).ct: $!";

	foreach my $i ( 0..$group_size) { 
		print $file join(" ", @{ $cayley_table[$i] }) . "\n";
	}
}

sub find_neutral_element
{
	my ($group_ref, $zp) = @_;

	my $eye = PDL::Matrix->pdl([[1,0],[0,1]]);

	foreach my $i ( 0..$#{ $group_ref } ) {
		if(all $group_ref->[$i] == $eye) {
			return $i;
		}
	}
}

sub init_group
{
	my ($group_ref, $zp) = @_;

	print "##############################################################################################\n";
	print "Zp: $zp\n";
	print "Order of SL(2,$zp): " . get_order_of_SL(2,$zp) . "\n";	
	print "Filling up arithmetic tables of finite field: ";
	fill_finite_field_arithmetic_tables($zp);
	print "\t\t\t\t\t\t[DONE]\n";
	print "Generating group elements: ";
	push @{ $group_ref }, generate_SL_group($zp);
	print "\t\t\t\t\t\t\t\t[DONE]\n";
	print "Looking for involutions: ";
	push @{ $group_ref }, find_involutions($group_ref->[0], $zp);
	print "\t\t\t\t\t\t\t\t[DONE]\n";
	print "Looking for neutral element: ";
	push @{ $group_ref }, find_neutral_element($group_ref->[0], $zp);
	print "\t\t\t\t\t\t\t\t[DONE]\n";
	print "Computing order of elements: ";
	push @{ $group_ref }, compute_order_set($group_ref->[0], $zp);
	print "\t\t\t\t\t\t\t\t[DONE]\n";
	print "##############################################################################################\n";
}

sub search_graphs_with_diameter
{
	my ($field_bound, $diameter) = @_;

	srand time;
	my $number_of_forks = 8;
	my $hash_table_size = 154485863;
	my $number_of_generated_graphs = 1000;
	my $time_limit = 10; # seconds

	my $nth_prime = 5;
	while((my $zp = get_nth_prime($nth_prime)) < $field_bound) {
		my @group;
		my $zp = get_nth_prime($nth_prime);
		init_group(\@group, $zp);
		my $moore_degree = int(sqrt($#{ $group[0] })) + 1;
		my $degree = int($moore_degree * 1.25) + 4;

		if($degree % 2) {
			$degree -= 1;	
		}	
		while(!check_random_graphs(\@group, $zp, $degree, $number_of_forks, $hash_table_size, $number_of_generated_graphs, $time_limit, $diameter)) {
			$degree += 2;
			print "##############################################################################################\n" . 
				  "Haven't found anything in SL(2,$zp) with order " . get_order_of_SL(2,$zp) . "\n" . 
				  "Going forward: " . ($degree - $moore_degree) . "\n" .
				  "Number of generated graphs: $number_of_generated_graphs\n" .
				  "Time limit: $time_limit\n" .
				  "Moore degree: $moore_degree\n" .
				  "Size of generating set: $degree\n" .
			      "##############################################################################################\n";

		}

		my $step_back = 1;
		my $adjusted_time_limit = 4 * $time_limit;
		print "##############################################################################################\n" . 
			  "Found something in SL(2,$zp) with order " . get_order_of_SL(2,$zp) . "\n" .
			  "Number of generated graphs: $number_of_generated_graphs\n" . 
			  "Moore degree: $moore_degree\n" .
			  "Size of generating set: $degree\n\n" .
			  "Going backwards taking $step_back. step back\n" .
			  "Number of generated graphs: " . (2 * $step_back * $number_of_generated_graphs) . "\n" .
			  "Time limit: " . $adjusted_time_limit . "\n" .
			  "Moore degree: $moore_degree\n" .
			  "Size of generating set: " . ($degree - $step_back * 2) .  "\n" .
			  "##############################################################################################\n";
		while(check_random_graphs(\@group, 
								  $zp, 
								  $degree - $step_back * 2, 
								  $number_of_forks, 
								  $hash_table_size, 
								  2 * $step_back * $number_of_generated_graphs, 
								  $adjusted_time_limit, 
								  $diameter)) {
			
			$step_back++;
			if(2 * $adjusted_time_limit > 5400) {
				$adjusted_time_limit = 5400;
			} else {
				$adjusted_time_limit *= 3;
			}
			print "##############################################################################################\n" . 
			      "Found something in SL(2,$zp) with order " . get_order_of_SL(2,$zp) . "\n" .
				  "Going backwards taking $step_back. step back\n" .
				  "Number of generated graphs: " . (2 * $step_back * $number_of_generated_graphs) . "\n" .
				  "Time limit: " . $adjusted_time_limit . "\n" .
			  	  "Moore degree: $moore_degree\n" .
				  "Size of generating set: ". ($degree - $step_back * 2) . "\n" .
			      "##############################################################################################\n";
		}
		$nth_prime++;
	}
}

sub search_graphs_with_girth
{
	my ($field_bound, $diameter, $property) = @_;

	srand time;
	my $number_of_forks = 8;
	my $hash_table_size = 154485863;
	my $number_of_generated_graphs = 50000;
	my $time_limit = 60; # seconds

	my $nth_prime = 3;
	while((my $zp = get_nth_prime($nth_prime)) < $field_bound) {
		my @group;
		my $zp = get_nth_prime($nth_prime);
		init_group(\@group, $zp);
		my $moore_degree;	# doplnit 
		my $degree; # doplnit

		$nth_prime++;
	}
}

sub generate_one_graph
{
	srand time;
	my $number_of_forks = 0;
	my $hash_table_size = 154485863;
	my $number_of_generated_graphs = 5;
	my $time_limit = 3600; # seconds
	my $zp = get_nth_prime(3);
	my @group;
	init_group(\@group, $zp);
	my $degree = int(sqrt($#{ $group[0] }));
	my @generating_set;

	print "Size: " . $#{ $group[0] } . "\n";
	my $m = $group[0]->[ $#{ $group[0] } - 4 ];
	push @generating_set, $m; 

	print "Generating set\n";
	my $generating_set_ref = get_random_generating_set(\@group, $zp, 1);
	print Dumper $generating_set_ref;
	<STDIN>;
	print "Generating cayley graph\n";
	my @cayley_graph = generate_cayley_graph(\@generating_set, $zp, $hash_table_size);
	

	print "Checking girth\n";
	my $girth = check_girth(@cayley_graph, 20);
	print "Girth is: $girth\n";
	print "Generating normal graph\n";
	my @graph = generate_graph_from_cayley_graph(@cayley_graph);
	print "Making graphical output\n";
	make_graphical_output(@graph, "test_for_girth");
	print "Fin\n";
}



search_graphs_with_diameter(99, 2);
