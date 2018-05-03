1 function cayley_graph_generation(generating_set[])
2 {
3     push all from generating_set[] to stack[]
4
5     foreach element in generating_set[]
6         generating_nodes[ element ] = element
7
8     current_node = first element of stack[]
9   
10    while stack[] not empty
11        foreach generating_element in generating_set[]
12            result = current_node x generating_element % Zp
13            cayley_graph[ current_node ] = result
14
15        if generating_nodes[ result ] is empty
16            push stack[], result
17            generating_nodes[ result ] = result
18
19        shift to the left stack[]
20        current_node = first element of stack[]
21
22    return cayley_graph[]
21}
