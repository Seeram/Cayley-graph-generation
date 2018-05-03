1  function find_cycle(generating_set[], girth)
2  { 
3  	foreach var = variation of indeces of generating_set with length girth
4 		node = generating_set[ var[0] ] x ... x genearating_set[ var[girth] ]
5 		if node equal to eye matrix
6 			return found cycle
7 	
8 	return cycle not found
9  }
10
11 function check_girth(generating_set[], girth) 
12 {
13	if(find_cycle(generating_set[], grith) {
14		foreach i in ( 3..girth - 1 )	{
15			if(find_cycle(generating_set[], i)) {
16				return has not given girth
17			}
18		}
19		return graph has given girth 
20	} else {
21		return has not given girth
22	}
23 }
