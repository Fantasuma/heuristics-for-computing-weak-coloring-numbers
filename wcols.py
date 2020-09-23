import networkx as nx
from tabulate import tabulate
import itertools
from collections import defaultdict, namedtuple
import math
import time
import pickle
import os
import random
import statistics
import concurrent.futures

def read_graph(file: str):
    g = nx.Graph()
    with open(file, "r") as f:
        g.add_edges_from([line.split() for line in f if line[0] != "#"])
    return g

def save_obj(obj, name):
    with open('obj/'+ name + '.pkl', 'wb') as f:
        pickle.dump(obj, f, pickle.HIGHEST_PROTOCOL)

def load_obj(name):
    with open('obj/' + name + '.pkl', 'rb') as f:
        return pickle.load(f)

def wreach_to_wcol(wreach: dict):
    return len(max(wreach.values(), key=len))

def compute_all_wreach(g: nx.Graph, L: dict, R: int, is_forb: list = []):
    result = defaultdict(list)

    for root in g.nodes:
        cluster = compute_single_cluster(g, L, R, root, is_forb)
        for v in cluster:
            result[int(v)].append(root)
    # for key, value in result.items():
    #     print(f"{key}: {value}")
    return result

def compute_single_cluster(g: nx.Graph, L: dict, R: int, root: str, is_forb: list = []):
    dis = defaultdict(lambda: None)
    root = str(root)
    result = []

    if len(is_forb) > 0 and is_forb[root] > 0:
        return result
    
    dis[root] = 0
    queue = [root]

    for current in queue:
        result.append(current)

        if dis[current] == R:
            continue

        for neighbor in g[str(current)]:
            if dis[neighbor] == None and L[int(neighbor)] > L[int(root)] and not neighbor in is_forb:
                queue.append(neighbor)
                dis[neighbor] = dis[current] + 1    
    return result

def compute_all_dependencies(g: nx.Graph, R: int, less_than, exclude_self = True):
    result = defaultdict(list)

    for root in g.nodes:
        cluster = compute_cluster_dependencies(g, R, root, less_than)
        for v in (v for v in cluster if v != root or not exclude_self):
            result[v].append(root)
    return result

def compute_cluster_dependencies(g: nx.Graph, R: int, root: int, less_than):
    root = str(root)
    result = []

    distance = defaultdict(lambda: None)
    distance[root] = 0

    queue = [root]

    for current in queue:
        result.append(current)

        if distance[current] == R:
            continue

        for neighbor in g[str(current)]:
            if distance[neighbor] == None and not less_than(neighbor, root):
                distance[neighbor] = distance[current] + 1
                queue.append(neighbor)
    return result

def add_edge(graph, a, b):
    graph.add_edge(a, b)
    return graph

def update_reaches(g: nx.Graph, R: int, dependencies: nx.DiGraph, less_than, current_reaches: dict, new_edge):
    to_update = nx.descendants(dependencies, new_edge[1])
    to_update.add(new_edge[1])

    for node in current_reaches.keys():
        current_reaches[node] = [n for n in current_reaches[node] if not n in to_update]

    for node in to_update:
        cluster = compute_cluster_dependencies(g, R, node, less_than)
        for v in (v for v in cluster if v != node):
            current_reaches[v].append(node)

    return current_reaches

def wreach_left(g: nx.Graph, R: int):
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], nx.degree(g, element), -int(element))
        return sort_key 

    order = []
    wreaches = defaultdict(lambda: 0)
    verts = [x[0] for x in sorted(g.degree, key=lambda x: x[1], reverse=True)]

    while len(verts) > 0:    
        current = max(verts, key=get_sort_key(g, wreaches))
        verts.remove(current)        
        
        order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")
    return order

def tie_l_rem_deg(g: nx.Graph, R: int):
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, reduced: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], nx.degree(reduced, element), nx.degree(g, element), -int(element))
        return sort_key 

    reduced = g.copy()
    order = []
    wreaches = defaultdict(lambda: 0)
    verts = [x[0] for x in sorted(g.degree, key=lambda x: x[1], reverse=True)]

    while len(verts) > 0:    
        current = max(verts, key=get_sort_key(g, reduced, wreaches))
        verts.remove(current)        
        reduced.remove_node(current)
        
        order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")
    return order

def wreach_left_pure(g: nx.Graph, R: int):
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], -int(element))
        return sort_key 

    order = []
    wreaches = defaultdict(lambda: 0)
    verts = [x[0] for x in sorted(g.degree, key=lambda x: x[1], reverse=True)]

    while len(verts) > 0:    
        current = max(verts, key=get_sort_key(g, wreaches))
        verts.remove(current)        
        
        order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")
    return order

def reach_alt(g: nx.Graph, R: int):
    # left
    def get_left_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_left_sort_key(g: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], nx.degree(g, element), -int(element))
        return sort_key 
    
    # right
    # turns out this needs no setup

    # function

    verts = list(g.nodes())
    left_order = []
    wreaches = defaultdict(lambda: 0)
    right_order = []
    sreaches = { node: set(list(g[node]) + [node]) for node in verts }
    
    while len(verts) > 0:
        # left
        current = max(verts, key=get_left_sort_key(g, wreaches))
        verts.remove(current)        
        
        left_order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_left_less_than(g, wreaches, left_order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")

        if len(verts) == 0:
            break

        # right
        current = min(verts, key=lambda element: (len(sreaches[element]), len(g[element]), int(element)))
        verts.remove(current)
        right_order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in right_order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")

    return left_order + right_order

def reach_alt_assist(g: nx.Graph, R: int):
    # left
    def get_left_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_left_sort_key(g: nx.Graph, wreaches: dict, sreaches: dict):    
        def sort_key(element):
            return (wreaches[element], nx.degree(g, element), sreaches[element], -int(element))
        return sort_key 
    
    # right
    # turns out this needs no setup

    # function

    verts = list(g.nodes())
    left_order = []
    wreaches = defaultdict(lambda: 0)
    right_order = []
    sreaches = { node: set(list(g[node]) + [node]) for node in verts }
    
    while len(verts) > 0:
        # left
        current = max(verts, key=get_left_sort_key(g, wreaches, sreaches))
        verts.remove(current)        
        
        left_order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_left_less_than(g, wreaches, left_order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")

        if len(verts) == 0:
            break

        # right
        current = min(verts, key=lambda element: (len(sreaches[element]), len(g[element]), wreaches[element], int(element)))
        verts.remove(current)
        right_order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in right_order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")

    return left_order + right_order

def reach_alt_assist_a(g: nx.Graph, R: int):
    # left
    def get_left_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_left_sort_key(g: nx.Graph, wreaches: dict, sreaches: dict):    
        def sort_key(element):
            return (wreaches[element], sreaches[element], nx.degree(g, element), -int(element))
        return sort_key 
    
    # right
    # turns out this needs no setup

    # function

    verts = list(g.nodes())
    left_order = []
    wreaches = defaultdict(lambda: 0)
    right_order = []
    sreaches = { node: set(list(g[node]) + [node]) for node in verts }
    
    while len(verts) > 0:
        # left
        current = max(verts, key=get_left_sort_key(g, wreaches, sreaches))
        verts.remove(current)        
        
        left_order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_left_less_than(g, wreaches, left_order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")

        if len(verts) == 0:
            break

        # right
        current = min(verts, key=lambda element: (len(sreaches[element]), wreaches[element], len(g[element]), int(element)))
        verts.remove(current)
        right_order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in right_order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")

    return left_order + right_order

def reach_secondhalf_rl(g: nx.Graph, R: int):
    order = sreach_right(g, R)

    # left setup
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], nx.degree(g, element), -int(element))
        return sort_key 
    
    wreaches = defaultdict(lambda: 0)
    order = order[:len(order) // 2]
    verts = [node for node in g.nodes() if node not in order]

    for current in order:        
        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1

    while len(verts) > 0:    
        current = max(verts, key=get_sort_key(g, wreaches))
        verts.remove(current)        
        
        order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")
    return order
    
def reach_secondhalf_lr(g: nx.Graph, R: int):
    order = wreach_left(g, R)
    
    order = order[len(order) // 2:]
    verts = [node for node in g.nodes() if node not in order]
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }

    tmp_order = []
    for current in reversed(order):
        tmp_order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in tmp_order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)

    while len(verts) > 0:
        current = min(verts, key=lambda element: (len(sreaches[element]), len(g[element]), int(element)))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")
    return order

def tie_r_rev_deg_pl(g: nx.Graph, R: int):
    other_order = wreach_left(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }
    
    order = []
    verts = list(g.nodes())
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }

    while len(verts) > 0:
        current = min(verts, key=lambda element: (len(sreaches[element]), g.subgraph(order + [element]).degree(element), g.degree(element), -other_order[element]))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")
    return order

def tie_r_rev_deg(g: nx.Graph, R: int):    
    order = []
    verts = list(g.nodes())
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }

    while len(verts) > 0:
        current = min(verts, key=lambda element: (len(sreaches[element]), g.subgraph(order + [element]).degree(element), g.degree(element)))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")
    return order

def order_assist_lr(g: nx.Graph, R: int):
    other_order = wreach_left(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }
    
    order = []
    verts = list(g.nodes())
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }

    while len(verts) > 0:
        current = min(verts, key=lambda element: (len(sreaches[element]), len(g[element]), -other_order[element]))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")
    return order
    
def order_assist_lr_aggressive(g: nx.Graph, R: int):
    other_order = wreach_left(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }
    
    order = []
    verts = list(g.nodes())
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }

    while len(verts) > 0:
        current = min(verts, key=lambda element: (len(sreaches[element]), -other_order[element], len(g[element])))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")
    return order

def order_assist_rl(g: nx.Graph, R: int):
    other_order = sreach_right(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    # left setup
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], nx.degree(g, element), -other_order[element])
        return sort_key 
    
    wreaches = defaultdict(lambda: 0)
    order = []
    verts = list(g.nodes())

    while len(verts) > 0:    
        current = max(verts, key=get_sort_key(g, wreaches))
        verts.remove(current)        
        
        order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")
    return order

def tie_l_rem_pr(g: nx.Graph, R: int):
    other_order = sreach_right(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    reduced = g.copy()

    # left setup
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], nx.degree(g, element), -other_order[element])
        return sort_key 
    
    wreaches = defaultdict(lambda: 0)
    order = []
    verts = list(g.nodes())

    while len(verts) > 0:    
        current = max(verts, key=get_sort_key(reduced, wreaches))
        verts.remove(current)        
        reduced.remove_node(current)
        
        order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")
    return order
    
def order_assist_rl_aggressive(g: nx.Graph, R: int):
    other_order = sreach_right(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    # left setup
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], -other_order[element])
        return sort_key 
    
    wreaches = defaultdict(lambda: 0)
    order = []
    verts = list(g.nodes())

    while len(verts) > 0:    
        current = max(verts, key=get_sort_key(g, wreaches))
        verts.remove(current)        
        
        order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")
    return order

def sreach_right(g: nx.Graph, R: int):
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    order = []
    verts = list(g.nodes)

    while len(verts) > 0:
        current = min(verts, key=lambda element: (len(sreaches[element]), len(g[element]), int(element)))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")
    return order

def sreach_right_pure(g: nx.Graph, R: int):
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    order = []
    verts = list(g.nodes)

    while len(verts) > 0:
        current = min(verts, key=lambda element: (len(sreaches[element]), int(element)))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
        # print(f"picked {current} - remaining {len(verts)}")
    return order

def tie_r_rev_deg(g: nx.Graph, R: int):

    # left setup
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, order, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], g.subgraph(order + [element]).degree(element), nx.degree(g, element), element) 
        return sort_key 
    
    wreaches = defaultdict(lambda: 0)
    order = []
    verts = list(g.nodes())

    while len(verts) > 0:    
        current = max(verts, key=get_sort_key(g, order, wreaches))
        verts.remove(current)        
        
        order.append(current)        

        cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
        # print(f"picked {current} - cluster: {len(cluster)}; remaining {len(verts)}")
    return order

def confidence(g: nx.Graph, R: int):
    # left
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than

    # main 
    wreaches = defaultdict(lambda: 0)
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    g_reduced = g.copy()
    verts = list(g.nodes)
    order_l = []
    order_r = []

    while len(verts) > 1:
        # selection in algorithms
        values_wreach = sorted(verts, reverse=True, key=lambda node: wreaches[node])[:2]
        values_sreach = sorted(verts, key=lambda element: len(sreaches[element]))[:2]
        values_degree = sorted(verts, reverse=True, key=lambda node: g_reduced.degree(node))[:2]
        values_reverse = sorted(verts, key=lambda node: g.subgraph(order_r + [node]).degree(node))[:2]

        # confidence values
        confidence_wreach = wreaches[values_wreach[0]] - wreaches[values_wreach[1]]
        confidence_sreach = len(sreaches[values_sreach[1]]) - len(sreaches[values_sreach[0]])
        confidence_degree = g_reduced.degree(values_degree[0]) - g_reduced.degree(values_degree[1])
        confidence_reverse = g.subgraph(order_r + [values_reverse[1]]).degree(values_reverse[1]) - g.subgraph(order_r + [values_reverse[0]]).degree(values_reverse[0])

        # selection of algorithms
        confidences = [confidence_wreach, confidence_sreach, confidence_degree, confidence_reverse]
        confidence_max = max(confidences)

        if confidence_max == confidence_sreach:
            current = values_sreach[0]
            left = False
        elif confidence_max == confidence_wreach:
            current = values_wreach[0]
            left = True
        elif confidence_max == confidence_degree:
            current = values_degree[0]
            left = True
        elif confidence_max == confidence_reverse:
            current = values_reverse[0]
            left = False
        else:
            current = values_sreach[0]
            left = False

        verts.remove(current)

        # update
        if left:
            order_l.append(current) 

            cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order_l))
            for vert in cluster:
                wreaches[vert] += 1

            g_reduced.remove_node(current)
        
        else:
            order_r.insert(0, current)

            distance = defaultdict(lambda: None)
            at_distance = defaultdict(list)
            distance[current] = 0
            queue = [current]
            for node in queue:
                for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                    distance[neighbor] = distance[node] + 1
                    if not neighbor in order_r:
                        at_distance[distance[neighbor]].append(neighbor)
                        sreaches[neighbor].remove(current)
                    elif distance[neighbor] < R:
                        queue.append(neighbor)
            for r1 in range(1, R):
                for r2 in range(1, R + 1 - r1):
                    for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                        sreaches[v1].add(v2)

    return order_l + verts + order_r

def confidence_deg(g: nx.Graph, R: int):
    # left
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than

    # main 
    wreaches = defaultdict(lambda: 0)
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    g_reduced = g.copy()
    verts = list(g.nodes)
    order_l = []
    order_r = []

    while len(verts) > 1:
        # selection in algorithms
        values_wreach = sorted(verts, reverse=True, key=lambda node: wreaches[node])[:2]
        values_sreach = sorted(verts, key=lambda element: len(sreaches[element]))[:2]
        values_degree = sorted(verts, reverse=True, key=lambda node: g_reduced.degree(node))[:2]
        values_reverse = sorted(verts, key=lambda node: g.subgraph(order_r + [node]).degree(node))[:2]
        values_deg_l = sorted(verts, reverse=True, key=lambda node: g.degree(node))[:2]
        values_deg_r = sorted(verts, key=lambda node: g.degree(node))[:2]

        # confidence values
        confidence_wreach = wreaches[values_wreach[0]] - wreaches[values_wreach[1]]
        confidence_sreach = len(sreaches[values_sreach[1]]) - len(sreaches[values_sreach[0]])
        confidence_degree = g_reduced.degree(values_degree[0]) - g_reduced.degree(values_degree[1])
        confidence_reverse = g.subgraph(order_r + [values_reverse[1]]).degree(values_reverse[1]) - g.subgraph(order_r + [values_reverse[0]]).degree(values_reverse[0])
        confidence_deg_l = g.degree(values_deg_l[0]) - g.degree(values_deg_l[1])
        confidence_deg_r = g.degree(values_deg_r[1]) - g.degree(values_deg_r[0])

        # selection of algorithms
        confidences = [confidence_wreach, confidence_sreach, confidence_degree, confidence_reverse, confidence_deg_l, confidence_deg_r]
        confidence_max = max(confidences)

        if confidence_max == confidence_sreach:
            current = values_sreach[0]
            left = False
        elif confidence_max == confidence_wreach:
            current = values_wreach[0]
            left = True
        elif confidence_max == confidence_degree:
            current = values_degree[0]
            left = True
        elif confidence_max == confidence_reverse:
            current = values_reverse[0]
            left = False
        elif confidence_max == confidence_deg_l:
            current = values_deg_l[0]
            left = True
        elif confidence_max == confidence_deg_r:
            current = values_deg_r[0]
            left = False
        else:
            current = values_sreach[0]
            left = False

        verts.remove(current)

        # update
        if left:
            order_l.append(current) 

            cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order_l))
            for vert in cluster:
                wreaches[vert] += 1

            g_reduced.remove_node(current)
        
        else:
            order_r.insert(0, current)

            distance = defaultdict(lambda: None)
            at_distance = defaultdict(list)
            distance[current] = 0
            queue = [current]
            for node in queue:
                for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                    distance[neighbor] = distance[node] + 1
                    if not neighbor in order_r:
                        at_distance[distance[neighbor]].append(neighbor)
                        sreaches[neighbor].remove(current)
                    elif distance[neighbor] < R:
                        queue.append(neighbor)
            for r1 in range(1, R):
                for r2 in range(1, R + 1 - r1):
                    for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                        sreaches[v1].add(v2)

    return order_l + verts + order_r

def confidence_last(g: nx.Graph, R: int):
    # left
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than

    # main 
    wreaches = defaultdict(lambda: 0)
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    g_reduced = g.copy()
    verts = list(g.nodes)
    order_l = []
    order_r = []

    while len(verts) > 1:
        # selection in algorithms
        values_wreach = sorted(verts, reverse=True, key=lambda node: wreaches[node])
        values_sreach = sorted(verts, key=lambda element: len(sreaches[element]))
        values_degree = sorted(verts, reverse=True, key=lambda node: g_reduced.degree(node))
        values_reverse = sorted(verts, key=lambda node: g.subgraph(order_r + [node]).degree(node))

        # confidence values
        confidence_wreach = wreaches[values_wreach[0]] - wreaches[values_wreach[-1]]
        confidence_sreach = len(sreaches[values_sreach[-1]]) - len(sreaches[values_sreach[0]])
        confidence_degree = g_reduced.degree(values_degree[0]) - g_reduced.degree(values_degree[-1])
        confidence_reverse = g.subgraph(order_r + [values_reverse[-1]]).degree(values_reverse[-1]) - g.subgraph(order_r + [values_reverse[0]]).degree(values_reverse[0])

        # selection of algorithms
        confidences = [confidence_wreach, confidence_sreach, confidence_degree, confidence_reverse]
        confidence_max = max(confidences)

        if confidence_max == confidence_sreach:
            current = values_sreach[0]
            left = False
        elif confidence_max == confidence_wreach:
            current = values_wreach[0]
            left = True
        elif confidence_max == confidence_degree:
            current = values_degree[0]
            left = True
        elif confidence_max == confidence_reverse:
            current = values_reverse[0]
            left = False
        else:
            current = values_sreach[0]
            left = False

        verts.remove(current)

        # update
        if left:
            order_l.append(current) 

            cluster = compute_cluster_dependencies(g, R, current, get_less_than(g, wreaches, order_l))
            for vert in cluster:
                wreaches[vert] += 1

            g_reduced.remove_node(current)
        
        else:
            order_r.insert(0, current)

            distance = defaultdict(lambda: None)
            at_distance = defaultdict(list)
            distance[current] = 0
            queue = [current]
            for node in queue:
                for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                    distance[neighbor] = distance[node] + 1
                    if not neighbor in order_r:
                        at_distance[distance[neighbor]].append(neighbor)
                        sreaches[neighbor].remove(current)
                    elif distance[neighbor] < R:
                        queue.append(neighbor)
            for r1 in range(1, R):
                for r2 in range(1, R + 1 - r1):
                    for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                        sreaches[v1].add(v2)

    return order_l + verts + order_r

def aggregate_left(g: nx.Graph, R: int):
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than

    orig_g = g
    g = g.copy()
    verts = list(g.nodes)
    order = []
    wreaches = defaultdict(lambda: 0)

    while len(verts) > 0:
        current = max(verts, key=lambda node: g.degree(node) + wreaches[node])
        verts.remove(current)
        order.append(current)
        g.remove_node(current)

        cluster = compute_cluster_dependencies(orig_g, R, current, get_less_than(orig_g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
    return order

def aggregate_left_deg(g: nx.Graph, R: int):
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than

    orig_g = g
    g = g.copy()
    verts = list(g.nodes)
    order = []
    wreaches = defaultdict(lambda: 0)

    while len(verts) > 0:
        current = max(verts, key=lambda node: g.degree(node) + wreaches[node] + orig_g.degree(node) / 10)
        verts.remove(current)
        order.append(current)
        g.remove_node(current)

        cluster = compute_cluster_dependencies(orig_g, R, current, get_less_than(orig_g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
    return order

def aggregate_right(g: nx.Graph, R: int):
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: g.subgraph(order + [node]).degree(node) + len(sreaches[node]))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
    return order

def aggregate_right_deg(g: nx.Graph, R: int):
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: g.subgraph(order + [node]).degree(node) + len(sreaches[node]) + g.degree(node) / 10)
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
    return order

def degree_remove(g: nx.Graph, R: int):
    g = g.copy()
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = max(verts, key=lambda node: g.degree(node))
        verts.remove(current)
        order.append(current)
        g.remove_node(current)
    return order

def tie_rem_deg(g: nx.Graph, R: int):
    orig = g
    g = g.copy()
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = max(verts, key=lambda node: (g.degree(node), orig.degree(node)))
        verts.remove(current)
        order.append(current)
        g.remove_node(current)
    return order

def degree_remove_assist_l(g: nx.Graph, R: int):
    other_order = wreach_left(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    g = g.copy()
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = max(verts, key=lambda node: (g.degree(node), -other_order[node]))
        verts.remove(current)
        order.append(current)
        g.remove_node(current)
    return order

def degree_remove_assist_r(g: nx.Graph, R: int):
    other_order = sreach_right(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    g = g.copy()
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = max(verts, key=lambda node: (g.degree(node), -other_order[node]))
        verts.remove(current)
        order.append(current)
        g.remove_node(current)
    return order

def degree_remove_conassist_l(g: nx.Graph, R: int):
    def get_less_than(g: nx.Graph, wreaches: dict, order: list):
        def less_than(a: str, b: str):
            if a in order:
                if b in order:
                    return order.index(a) < order.index(b)
                return True
            elif b in order:
                return False
            return False
        return less_than
    
    def get_sort_key(g: nx.Graph, wreaches: dict):    
        def sort_key(element):
            return (wreaches[element], nx.degree(g, element), -int(element))
        return sort_key 

    orig_g = g
    g = g.copy()
    verts = list(g.nodes)
    order = []
    wreaches = defaultdict(lambda: 0)

    while len(verts) > 0:
        current = max(verts, key=lambda node: (g.degree(node), get_sort_key(orig_g, wreaches)(node)))
        verts.remove(current)
        order.append(current)
        g.remove_node(current)

        cluster = compute_cluster_dependencies(orig_g, R, current, get_less_than(orig_g, wreaches, order))
        for vert in cluster:
            wreaches[vert] += 1
    return order

def degree_remove_reverse(g: nx.Graph, R: int):
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: (g.subgraph(order + [node]).degree(node), g.degree(node)))
        verts.remove(current)
        order.insert(0, current)
    return order

def degree_remove_reverse_assist_l(g: nx.Graph, R: int):
    other_order = wreach_left(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: (g.subgraph(order + [node]).degree(node), g.degree(node), -other_order[node]))
        verts.remove(current)
        order.insert(0, current)
    return order

def degree_remove_reverse_assist_la(g: nx.Graph, R: int):
    other_order = wreach_left(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: (g.subgraph(order + [node]).degree(node), -other_order[node]))
        verts.remove(current)
        order.insert(0, current)
    return order

def degree_remove_reverse_assist_r(g: nx.Graph, R: int):
    other_order = sreach_right(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: (g.subgraph(order + [node]).degree(node), g.degree(node), -other_order[node]))
        verts.remove(current)
        order.insert(0, current)
    return order

def degree_remove_reverse_assist_ra(g: nx.Graph, R: int):
    other_order = sreach_right(g, R)
    other_order = { node: i for i, node in enumerate(other_order) }

    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: (g.subgraph(order + [node]).degree(node), -other_order[node]))
        verts.remove(current)
        order.insert(0, current)
    return order

def degree_remove_reverse_conassist_r(g: nx.Graph, R: int):
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: (g.subgraph(order + [node]).degree(node), g.degree(node), len(sreaches[node])))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
    return order

def degree_remove_reverse_conassist_ra(g: nx.Graph, R: int):
    sreaches = { node: set(list(g[node]) + [node]) for node in g.nodes }
    verts = list(g.nodes)
    order = []

    while len(verts) > 0:
        current = min(verts, key=lambda node: (g.subgraph(order + [node]).degree(node), len(sreaches[node]), g.degree(node)))
        verts.remove(current)
        order.insert(0, current)

        distance = defaultdict(lambda: None)
        at_distance = defaultdict(list)
        distance[current] = 0
        queue = [current]
        for node in queue:
            for neighbor in (neighbor for neighbor in g[node] if distance[neighbor] == None):
                distance[neighbor] = distance[node] + 1
                if not neighbor in order:
                    at_distance[distance[neighbor]].append(neighbor)
                    sreaches[neighbor].remove(current)
                elif distance[neighbor] < R:
                    queue.append(neighbor)
        for r1 in range(1, R):
            for r2 in range(1, R + 1 - r1):
                for v1, v2 in ((v1, v2) for v1, v2 in itertools.product(at_distance[r1], at_distance[r2]) if v1 != v2):
                    sreaches[v1].add(v2)
    return order

def degree(g: nx.Graph, R: int):
    return [node for node, _ in g.degree()]

def nodes_by_id(g: nx.Graph, R: int):
    return sorted(list(g.nodes()))

def random_order(g: nx.Graph, R: int):
    random.seed(22)
    l = list(g.nodes())
    random.shuffle(l)
    return l

def local_search(g: nx.Graph, R: int, order: dict):
    random.seed(22)
    k_min_old_tries = 1000
    k_min_new_tries = 6000

    n = len(g.nodes())
    best_order = order
    best_reaches = compute_all_wreach(g, order, R)
    best_wcol = wreach_to_wcol(best_reaches)

    last_old_update = 0
    phase = 0
    while phase < max([k_min_old_tries, 2 * last_old_update]):
        order = best_order.copy()
        current_worst = max(best_reaches.items(), key=lambda x: len(x[1]))[0]
        earlier_pos = random.randint(0, order[int(current_worst)])
        earlier_node = str(next(e for e in order.keys() if order[e] == earlier_pos))
        order[int(current_worst)], order[int(earlier_node)] = order[int(earlier_node)], order[int(current_worst)]
        reaches = compute_all_wreach(g, order, R)
        wcol = wreach_to_wcol(reaches)
        if wcol <= best_wcol:    # todo: investigate variants on this
            if wcol < best_wcol:
                # print(f"old({phase}) {best_wcol}->{wcol})")
                last_old_update = phase
                last_new_update = phase + 10 # Guarantee it's run
                best_wcol = wcol
            best_order = order
            best_reaches = reaches
        phase += 1
    
    order = best_order.copy()
    reaches = best_reaches
    reach_sizes = { node: len(reaches[int(node)]) for node in g.nodes() }
    clusters = { node: compute_single_cluster(g, order, R, node) for node in g.nodes() }
    queue = [(reach_sizes[node], node) for node in g.nodes()]

    random.seed(22)
    last_new_update = 0
    while phase < max([k_min_new_tries, 2 * last_new_update]):
        queue.sort()
        current_worst = queue[-random.randint(0, min([10, n]))]
        current_node = current_worst[1]
        target = max([1, reach_sizes[current_node] - random.randint(1, 4)])

        while reach_sizes[current_node] > target:
            current_pos = order[int(current_node)]
            earlier_pos = current_pos - 1
            earlier_node = str(next(e for e in order.keys() if order[e] == earlier_pos))
            for source in [current_node, earlier_node]:
                for to_update in clusters[source]:
                    queue.remove((reach_sizes[to_update], to_update))
                    reach_sizes[to_update] -= 1
                    queue.append((reach_sizes[to_update], to_update))
            order[int(current_node)], order[int(earlier_node)] = order[int(earlier_node)], order[int(current_node)]
            for source in [current_node, earlier_node]:
                clusters[source] = compute_single_cluster(g, order, R, source)
                for to_update in clusters[source]:
                    queue.remove((reach_sizes[to_update], to_update))
                    reach_sizes[to_update] += 1
                    queue.append((reach_sizes[to_update], to_update))

            queue.sort()
            wcol = queue[-1][0]
            if wcol < best_wcol:
                # print(f"new({phase}) {best_wcol}->{wcol} (using {[current_node, earlier_node]})")
                last_new_update = phase
                best_wcol = wcol
                best_order = order.copy()
        phase += 1
    return best_order

### Test Parameters
# Rs = [3]
Rs = range(1, 6)

small_sample = [
    "bergen.txtg", 
    "football.txtg",
    "planar600.txtg",
]

small_graphs = [
    "bergen.txtg",
    "dolphins.txtg",
    "football.txtg",
    "fvs002.txtg",
    "fvs020.txtg",
    "fvs033.txtg",
    "fvs047.txtg",
    "fvs051.txtg",
    "fvs066.txtg",
    "fvs097.txtg",
    "fvs099.txtg",
    "fvs100.txtg",
    "hex.txtg",
    "karate.txtg",
    "lesmiserables.txtg",
    "photoviz_dynamic.txtg",
    "planar302.txtg",
    "planar350.txtg",
    "planar400.txtg",
    "planar500.txtg",
    "planar600.txtg",
    "polbooks.txtg",
]
small_graphs = ["small/" + name for name in small_graphs]

medium_graphs = [
    "airlines.txtg",
    "clh-10-0.txtg",
    "cpan-distributions.txtg",
    "fvs021.txtg",
    "netscience.txtg",
    "planar2500.txtg",
    "sb-10-2.txtg",
    "celegans.txtg",
    "clh-10-1.txtg",
    "diseasome.txtg",
    "fvs023.txtg",
    "planar3000.txtg",
    "sp_data_school_day_2.txtg",
    "cl-10-0.txtg",
    "clh-10-2.txtg",
    "fvs004.txtg",
    "fvs052.txtg",
    "planar1302.txtg",
    "power.txtg",
    "cl-10-1.txtg",
    "codeminer.txtg",
    "fvs008.txtg",
    "fvs056.txtg",
    "planar1500.txtg",
    "sb-10-0.txtg",
    "yeast.txtg",
    "cl-10-2.txtg",
    "cpan-authors.txtg",
    "fvs014.txtg",
    "fvs078.txtg",
    "planar2000.txtg",
    "sb-10-1.txtg",
]
medium_graphs = ["medium/" + name for name in medium_graphs]

big_graphs = [
    "as20000102.txtg",
    "cl-12-1.txtg",
    "clh-12-1.txtg",
    "fvs001.txtg",
    "fvs040.txtg",
    "fvs074.txtg",
    "hep-th.txtg",
    "p2p-Gnutella04.txtg",
    "planar12000.txtg",
    "planar7002.txtg",
    "polblogs.txtg",
    "sb-12-1.txtg",
    "cl-12-0.txtg",
    "clh-12-0.txtg",
    "cond-mat.txtg",
    "fvs022.txtg",
    "fvs045.txtg",
    "fvs080.txtg",
    "planar10000.txtg",
    "planar15000.txtg",
    "planar8500.txtg",
    "sb-12-0.txtg",
]
big_graphs = ["big/" + name for name in big_graphs]

huge_graphs = [
    "ca-CondMat.txtg",
    "cit-HepPh.txtg",
    "cl-14-0.txtg",
    "email-Enron.txtg",
    "fvs041.txtg",
    "planar70000.txtg",
    "soc-Epinions1.txtg",
    "twittercrawl.txtg",
    "ca-HepPh.txtg",
    "cit-HepTh.txtg",
    "clh-14-0.txtg",
    "fvs037.txtg",
    "loc-brightkite_edges.txtg",
    "planar50002.txtg",
    "sb-14-0.txtg",
    "soc-Slashdot0811.txtg",
]
huge_graphs = ["huge/" + name for name in huge_graphs]

graph_files = small_graphs
graph_names = [filename.split("/")[-1] for filename in graph_files]

graphs = [(graph_name, read_graph("graphs/" + graph_file)) for graph_file, graph_name in zip(graph_files, graph_names)]

# Only works with unchanged parameters
load_stored = True
early_save = True
save_at_all = True
overwrite = False
thread_count = 8

print("Loading default optimal orders")
best_wcols = {}
if load_stored:
    best_wcols = load_obj("best_wcols")

# find current minimum
for graph_name, g in graphs:
    if all((graph_name, R) in best_wcols for R in Rs):
        print(f"{graph_name} cached, skipping")
        continue
    sizes = [ "small", "medium", "big", "huge" ]
    directories = ["graphs/" + size + "/orders/" for size in sizes]
    files = []
    for directory in directories:
        prefix = graph_name.split(".")[0].split("/")[-1]
        files += [directory + f for f in os.listdir(directory) if f.startswith(prefix)]
    files = (open(filename) for filename in files)
    contents = (f.readline() for f in files)
    orders = (content.split() for content in contents)
    Ls = [{ int(node): i for i, node in enumerate(order) } for order in orders if len(order) == len(g.nodes())]

    for R in Rs:
        if not (graph_name, R) in best_wcols:
            wcols = [wreach_to_wcol(compute_all_wreach(g, L, R)) for L in Ls]
            wcol = min(wcols)
            best_wcols[graph_name, R] = wcol
            if save_at_all and early_save:
                save_obj(best_wcols, "best_wcols")
        else:
            wcol = best_wcols[graph_name, R]
        print(f"{graph_name} - {R}: {wcol}")

if save_at_all:
    save_obj(best_wcols, "best_wcols")

### Try all algorithms
algorithms = [
    ("degree", degree),
    ("nodes_by_id", nodes_by_id),
    ("altn", reach_alt),
    ("altn-l-deg-r", reach_alt_assist),
    ("altn-l-r-deg", reach_alt_assist_a),
    ("second-rl", reach_secondhalf_rl),
    ("second-lr", reach_secondhalf_lr),
    ("tie-l-deg-pr", order_assist_rl),
    ("tie-r-deg-pl", order_assist_lr),
    ("tie-l-rem-pr", tie_l_rem_pr),
    ("tie-l-rem-deg", tie_l_rem_deg),    
    ("tie-l-pr", order_assist_rl_aggressive),
    ("tie-r-pl", order_assist_lr_aggressive),
    ("tie-r-rev-deg", tie_r_rev_deg),
    ("tie-r-rev-deg-pl", tie_r_rev_deg_pl),
    ("remove", degree_remove),
    ("tie-rem-deg", tie_rem_deg),
    ("tie-rem-pl", degree_remove_assist_l),
    ("tie-rem-pr", degree_remove_assist_r),
    ("tie-rem-left-deg", degree_remove_conassist_l),
    ("tie-rev-deg", degree_remove_reverse),
    ("tie-rev-deg-pl", degree_remove_reverse_assist_l),
    ("tie-rev-pl", degree_remove_reverse_assist_la),
    ("tie-rev-deg-pr", degree_remove_reverse_assist_r),
    ("tie-rev-pr", degree_remove_reverse_assist_ra),
    ("tie-rev-deg-right", degree_remove_reverse_conassist_r),
    ("tie-rev-right-deg", degree_remove_reverse_conassist_ra),
    ("random", random_order),
    ("conf-1", confidence),
    ("conf-last", confidence_last),
    ("conf-2", confidence_deg),
    ("agglr-rem-left", aggregate_left),
    ("agglr-rem-right-deg-10", aggregate_left_deg),
    ("aggrl-rev-right", aggregate_right),
    ("aggrl-rev-right-deg-10", aggregate_right_deg),
    ("left", wreach_left_pure),
    ("right", sreach_right_pure),
    ("tie-l-deg", wreach_left),
    ("tie-r-deg", sreach_right),
]

algorithm_names_pure = [name for name, _ in algorithms]
algorithm_names = algorithm_names_pure + [name + "-ls" for name, _ in algorithms]

wcols = {}
durations = {}
# if load_stored:    
#     wcols = load_obj("wcols")

def run_alg(gra, R, alg):
    def results_file(graph, R, name):
        return f"results/{graph}-{R}-{name}"

    def calculate_order(graph, R, name, f):
        print(f"{graph} - {R} - {name}   : starting...")
        timer = time.process_time()
        order = f()
        duration = time.process_time() - timer
        order_nodes = order
        if not type(order) is dict:
            order = { int(node): i for i, node in enumerate(order) }
        wcol = wreach_to_wcol(compute_all_wreach(g, order, R))
        with open(results_file(graph, R, name), "w") as f:
            f.write(f"{wcol} {duration}\n")
            f.write(" ".join(map(str, order_nodes)) + "\n")
        return (wcol, duration, order)   

    def load_order(graph, R, name, f):
        print(f"{graph} - {R} - {name}   : retrieving cache...")
        try:
            with open(results_file(graph, R, name), "r") as f:
                line = f.readline()
                split = line.split()
                wcol = int(split[0])
                duration = float(split[1])
                order = f.readline().split()
                order = { int(node): i for i, node in enumerate(order) }
                return (wcol, duration, order)
        except:
            print(f"{graph} - {R} - {name}   : loading failed, recualculating...")
            return calculate_order(graph, R, name, f)

    def resolve_alg(graph, R, name, f):
        if os.path.isfile(results_file(graph, R, name)):
            (wcol, duration, order) = load_order(graph, R, name, f)
        else:    
            (wcol, duration, order) = calculate_order(graph, R, name, f)

        print(f"{graph} - {R} - {name}: {wcol: 5d} ({duration:.2f}s)")
        return (wcol, duration, order)

    (graph, g) = gra
    (name, algorithm) = alg
    name_ls = name + "-ls"
    
    (wcol, duration, order) = resolve_alg(graph, R, name, lambda: algorithm(g, R))
    (wcol_ls, duration_ls, order_ls) = resolve_alg(graph, R, name_ls, lambda: local_search(g, R, order))

    return [((graph, R, name), (wcol, duration)), ((graph, R, name_ls), (wcol_ls, duration_ls))]

futures = []
with concurrent.futures.ProcessPoolExecutor(max_workers=thread_count) as executor:
    i = 1
    for (graph, g), (name, algorithm), R in itertools.product(graphs, algorithms,  reversed(list(Rs))):
        print(f"{graph} - {R} - {name}: added to queue")
        if thread_count == 1:
            futures.append(run_alg((graph, g), R, (name, algorithm)))
        else:
            futures.append(executor.submit(run_alg, (graph, g), R, (name, algorithm)))

    print("Starting calculations!")

    total_length = len(graph_names) * len(Rs) * len(algorithm_names)
    for future in futures:
        if thread_count != 1:
            future = future.result()
        for ((graph, R, name), (wcol, duration)) in future:
            wcols[graph, R, name] = wcol
            durations[graph, R, name] = duration
            if early_save and save_at_all:
                save_obj(wcols, "wcols")
            print(f"{i/total_length*100:6.2f}% - {graph} - {R} - {name}: {wcol: 5d} ({duration:.2f}s)")
            i += 1
            if wcol < best_wcols[graph, R]:
                print(f"Updating best from {best_wcols[graph, R]} to {wcol}")
                best_wcols[graph, R] = wcol
                save_obj(best_wcols, "best_wcols")

if save_at_all:
    save_obj(wcols, "wcols")
print("Finished!")

print("========== Results ==========")

for graph in graph_names:
    print(f"------ {graph} ------")
    headers = ["algorithm"] + list(Rs) + ["avg"]
    table = []
    for name in sorted(algorithm_names, key=lambda name: sum(wcols[graph, R, name] for R in Rs)):
        table.append([name] + [wcols[graph, R, name] for R in Rs] + [statistics.mean(wcols[graph, R, name] for R in Rs)])
    print(tabulate(table, headers=headers, tablefmt="github"))

print("========== Total ==========")

best_single = defaultdict(lambda: 0)
best_shared = defaultdict(lambda: 0)
for graph, R in itertools.product(graph_names, Rs):
    min_wcol = min(wcols[graph, R, name] for name in algorithm_names)
    best_algs = [name for name in algorithm_names if wcols[graph, R, name] == min_wcol]
    if len(best_algs) == 1:
        best_single[best_algs[0]] += 1
    elif len(best_algs) == 2 and (best_algs[0] + "-ls" == best_algs[1] or best_algs[1] + "-ls" == best_algs[0]):
        best_single[best_algs[0]] += 1
        best_single[best_algs[1]] += 1
    for name in best_algs:
        best_shared[name] += 1

averages = {}
avg_durations = {}
for name, R in itertools.product(algorithm_names, Rs):
    averages[name, R] = statistics.mean([wcols[graph, R, name] / best_wcols[graph, R] for graph in graph_names])
for name in algorithm_names:
    averages[name] = statistics.mean(averages[name, R] for R in Rs)
    avg_durations[name] = statistics.mean(durations[graph, R, name] for R in Rs for graph in graph_names)

# headers = ["algorithm"] + list(Rs) + ["avg", "<", "<=", "time"]
headers = ["algorithm"] + list(Rs) + ["avg", "time"]
table = []
for name in sorted(algorithm_names, key=lambda name: averages[name]):
    # row = [name] + [averages[name, R] for R in Rs] + [averages[name], best_single[name], best_shared[name], avg_durations[name]]
    row = [name] + [averages[name, R] for R in Rs] + [averages[name], avg_durations[name]]
    table.append(row)
print(tabulate(table, headers=headers, tablefmt="github"))
