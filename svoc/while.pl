1   push all from generating_set[] to stack[]
2   current_node = first element of stack[]
3
4   while stack[] not empty
5       foreach generating_element in generating_set[]
6           r = current_node x generating_element % zp
7           cayley_graph[ current_node ] = r
8           
9           if generating_nodes[r] is empty
10              push stack[], r
11              generating_nodes[r] = r
12
13      shift to the left stack[]
14
15      if stack[] not empty
16          current_node = first element of stack[]
