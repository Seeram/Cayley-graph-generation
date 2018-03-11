#!/usr/bin/env python

import numpy as np
import gmpy2

from graph_tool.all import *


generujuca_mnozina = list()
a = np.matrix('1 7;7 3')
b = np.matrix('2 0;1 2')

def print_set(set):
    for matrix in set: 
        print(matrix)


def get_nth_prime(x):
    n = 2
    for i in range(x):
        n = gmpy2.next_prime(n)
    return n

def hash_matrix(matrix, zp):
    val = 0
    for i in range(2):
        for j in range(2):
            val = zp * val + matrix[i,j] 

    return val

def make_matrix_label(matrix):
    return "((" + str(matrix[0,0]) + " " + str(matrix[0,1]) + ")(" + str(matrix[1,0]) + " " + str(matrix[1,1]) + "))"


def generate_subgroup(generating_set, zp):
        # Udrziavanie informacie o vrcholoch pomocou ktorych boli vygenerovane sucinom cez generujucu mnozinu dalsie vrcholy
    generating_matrices = dict()
        # LIFO datova struktura na udrzanie vrcholov ktore sa stanu generujucimi vrcholmi
    stack = list(generating_set)

    graph = Graph(directed=False)
    vertex_list = dict()
    vertex_label = graph.new_vertex_property("string")

    generating_matrix = generating_set[0]
    generating_matrices[hash_matrix(generating_matrix, zp)] = True

    v = graph.add_vertex()
    vertex_list[hash_matrix(generating_matrix, zp)] = v
    vertex_label[v] = make_matrix_label(generating_matrix)
    

    while stack:
        for generating_set_element in generating_set:
            multiplication_result = (generating_matrix * generating_set_element) % zp
            if hash_matrix(multiplication_result, zp) not in generating_matrices:
                stack.append(multiplication_result)

            if not (generating_matrix == multiplication_result).all():
                if hash_matrix(generating_matrix, zp) not in vertex_list:
                    source_v = graph.add_vertex()
                    vertex_list[hash_matrix(generating_matrix, zp)] = source_v
                    vertex_label[source_v] = make_matrix_label(generating_matrix)
                else:
                    source_v = vertex_list[hash_matrix(generating_matrix, zp)]

                if hash_matrix(multiplication_result, zp) not in vertex_list:
                    target_v = graph.add_vertex()
                    vertex_list[hash_matrix(multiplication_result, zp)] = target_v
                    vertex_label[target_v] = make_matrix_label(multiplication_result)
                else:
                    target_v = vertex_list[hash_matrix(multiplication_result, zp)]

                graph.add_edge(source_v, target_v)

        stack.pop(0)

        if stack:
            generating_matrix = stack[0]
            generating_matrices[hash_matrix(generating_matrix, zp)] = True
    
    print("Num vertices: " + str(graph.num_vertices()))
    raw_input()
    print("pocitam")
    graph_tool.stats.distance_histogram(graph)

#    graph.vertex_properties["name"] = vertex_label
#    graph_tool.draw.graphviz_draw(
#                graph,
#                vertex_text=graph.vertex_properties["name"],
#                layout="circo",
#                output="test.png"
#              )





gen_set = [np.matrix('2 0;1 3'), np.matrix('2 0;1 2'), np.matrix('2 4;2 3')]
generate_subgroup(gen_set, 11)
