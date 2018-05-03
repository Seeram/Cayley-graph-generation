1 function check_diameter(generating_set[], diameter) 
2 {
3 	push reached_nodes[], generating_set[]
4
5	foreach n in [ 2, ... ,diameter ]
6		foreach var = variation of indeces of generating_set with length n 
7			node = generating_set[ var[0] ] x ... x generating_set[ var[len] ]
8			push reached_nodes[], node
9       if reached_nodes[] contains all elements of group
10		    retrun cayley_graph has diameter n
11
12	retrun cayley_graph has bigger diameter
13}
