#!/usr/bin/env python

import itertools
import re
import pandas as pd
import numpy as np
import networkx as nx
import matplotlib
import matplotlib.pyplot as plt

from scipy.cluster.hierarchy import dendrogram, fcluster, leaves_list, linkage
from scipy.spatial import distance_matrix
from scipy.spatial import distance

def parse_event_types(eventtypes):
    if eventtypes == "":
        return []
    return re.split(', |\n', eventtypes)

# determine the high level app class this belongs in
def get_listener_class(listener):
    label = ""
    # get rid of long listener signature
    result = re.search('<(.*):', listener)
    label = result.group(1)
    # some names don't follow protocol
    if label.split('.')[2] == "net":
        label = label.split('.')[3]
    else:
        label = label.split('.')[2]
    return label

# get event kind from "event kind: event type"
def get_event_kind(event_concat):
    result = re.search('(.*): (.*)', event_concat)
    return result.group(1)

# Calculate SimRank
# code from https://stackoverflow.com/questions/9767773/calculating-simrank-using-networkx
# Fixed to adjust for networkx v2
def simrank(G, r=0.8, max_iter=100, eps=1e-4):

    nodes = list(G.nodes())
    nodes_i = {k: v for(k, v) in [(nodes[i], i) for i in range(0, len(nodes))]}

    sim_prev = np.zeros(len(nodes))
    sim = np.identity(len(nodes))

    for i in range(max_iter):
        if np.allclose(sim, sim_prev, atol=eps):
            break
        sim_prev = np.copy(sim)
        for u, v in itertools.product(nodes, nodes):
            if u is v:
                continue
            u_ns, v_ns = list(G.predecessors(u)), list(G.predecessors(v))
            # evaluating the similarity of current iteration nodes pair
            if len(u_ns) == 0 or len(v_ns) == 0: 
                # if a node has no predecessors then setting similarity to zero
                sim[nodes_i[u]][nodes_i[v]] = 0
            else:                    
                s_uv = sum([sim_prev[nodes_i[u_n]][nodes_i[v_n]] for u_n, v_n in itertools.product(u_ns, v_ns)])
                sim[nodes_i[u]][nodes_i[v]] = (r * s_uv) / (len(u_ns) * len(v_ns))

    return sim, nodes

def main():

    apps = {} # dict; app -> set(Event:EventType, ...)
    all_event_types = set() # universe of all Event:EventTypes

    with open("data.txt") as f:
        for l1,l2,l3,l4,l5 in itertools.izip_longest(*[f]*5):
            (listener, eventtypes, event, category, isrelevant) = (l1,l2,l3,l4,l5)
            
            listener = listener.splitlines()[0]
            eventtypes = eventtypes.splitlines()[0]
            event = event.splitlines()[0]
            category = category.splitlines()[0]
            isrelevant = isrelevant.splitlines()[0]
            listener = category[0] + ": " + get_listener_class(listener)
            
            if listener in apps:
                eventtypes = parse_event_types(eventtypes)
                newset = set()
                for eventtype in eventtypes:
                    eventtype_to_add = event + ": " + eventtype
                    if eventtype_to_add not in all_event_types:
                        all_event_types.add(eventtype_to_add)
                    newset.add(eventtype_to_add)
                apps[listener] = set(apps[listener].union(newset))
            else:
                eventtypes = parse_event_types(eventtypes)
                newset = set()
                for eventtype in eventtypes:
                    eventtype_to_add = event + ": " + eventtype
                    if eventtype_to_add not in all_event_types:
                        all_event_types.add(eventtype_to_add)
                    newset.add(eventtype_to_add)
                apps[listener] = newset
        
        # sorted list of event types so we can keep logical groupings
        sorted_event_types = sorted(list(all_event_types))
        sorted_apps = []
        for app_name, eventtypes in apps.iteritems():
            sorted_apps.append(app_name)
        sorted_apps = sorted(sorted_apps)
        
        matrix = [] # matrix of what we'll plot for data
        G = nx.DiGraph() # bipartite graph of apps -> event types
        G.add_node("T: ofagent")
        for app_name in sorted_apps:
            matrix_row = [] # row of our matrix, corresponding to an app
            for given_event_type in sorted_event_types:
                if given_event_type in apps[app_name]:
                    matrix_row.append(int(1))  # define presence = 1
                    G.add_edge(app_name, given_event_type)  # add to bipartite graph
                    G.add_edge(given_event_type, app_name)
                else:
                    matrix_row.append(int(0))  # define absence = 0
            matrix.append(matrix_row)
        
        ## PART 1: Event use table plot
        
        matrix_np = np.array(matrix)    # numpy matrix
        font = {'size'   : 5} 
        plt.rc('font', **font)
        fig, ax = plt.subplots()
        im = ax.imshow(matrix_np, cmap='gray_r', norm=matplotlib.colors.Normalize(vmin=0.0, vmax=1.0, clip=False))
        ax.set_xticks(np.arange(len(sorted_event_types)))
        ax.set_yticks(np.arange(len(sorted_apps)))
        ax.set_xticklabels(sorted_event_types)
        ax.set_yticklabels(sorted_apps)
        
        # get the app categories / event kinds to align well
        ax.hlines([.5, 1.5, 7.5, 12.5, 15.5, 16.5, 38.5], *ax.get_xlim(), colors='black', linewidth=0.5)
        ax.vlines([8.5, 10.5, 13.5, 17.5, 24.5, 27.5, 30.5, 36.5, 41.5, 43.5], *ax.get_ylim(), colors='black', linewidth=0.5)
            
        plt.setp(ax.get_xticklabels(), rotation=90, ha="right",
                rotation_mode="anchor")
        plt.setp(ax.get_yticklabels())
        dx = -1.5/72.; dy = 0/72. 
        offset = matplotlib.transforms.ScaledTranslation(dx, dy, fig.dpi_scale_trans)
        for label in ax.xaxis.get_majorticklabels():
            label.set_transform(label.get_transform() + offset)

        plt.xlabel("Event Kind: Event Type")
        plt.ylabel("App Category: App Name")
        fig.tight_layout()
        plt.savefig("event-use-table.pdf", bbox_inches='tight', pad_inches = 0)
        plt.clf()
        plt.close()
        
        ## PART 2: Hamming distance similarity matrix + dendrogram
        
        ##  Compute the Hamming distances of app X app, then use hierarchical
        ##  clustering to create a dendrogram of the clusters.
        
        ## Useful links:
        ##  http://www.econ.upf.edu/~michael/stanford/maeb7.pdf
        ##  https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.cluster.hierarchy.linkage.html
        ##  https://stackoverflow.com/questions/22081503/distance-matrix-creation-using-nparray-with-pdist-and-squareform
        ##  https://stats.stackexchange.com/questions/222492/any-distance-measures-that-are-more-useful-for-binary-data-clustering
        
        df = pd.DataFrame(matrix_np, index = sorted_apps, columns = sorted_event_types)
        df.to_csv(r'app-event-types.csv')
        
        distance_matrix_np = np.zeros((len(sorted_apps), len(sorted_apps)))
        for i in range(0, len(sorted_apps)):
            for j in range(0, len(sorted_apps)):
                distance_matrix_np[i, j] = distance.hamming(matrix_np[i], matrix_np[j])
                distance_matrix_np[j, i] = distance_matrix_np[i, j]
        
        df_hamming = pd.DataFrame(distance_matrix_np, index = sorted_apps, columns = sorted_apps)
        df_hamming.to_csv(r'app-event-similarity-hamming.csv')
        
        font = {'size'   : 6} 
        plt.rc('font', **font)
        fig, ax = plt.subplots()
        im = ax.imshow(distance_matrix_np, cmap='gray', norm=matplotlib.colors.Normalize(vmin=0.0, vmax=1.0, clip=False))
        ax.set_xticks(np.arange(len(sorted_apps)))
        ax.set_yticks(np.arange(len(sorted_apps)))
        ax.set_xticklabels(sorted_apps)
        ax.set_yticklabels(sorted_apps)
        plt.setp(ax.get_xticklabels(), rotation=90, ha="right",
                rotation_mode="anchor")
        plt.setp(ax.get_xticklabels(), rotation=90, ha="right",
                rotation_mode="anchor")
        dx = -3/72.; dy = 0/72. 
        offset = matplotlib.transforms.ScaledTranslation(dx, dy, fig.dpi_scale_trans)
        for label in ax.xaxis.get_majorticklabels():
            label.set_transform(label.get_transform() + offset)
        plt.xlabel("App Category: App Name")
        plt.ylabel("App Category: App Name")
        fig.tight_layout()
        plt.savefig("app-event-similarity-hamming.pdf", bbox_inches='tight', pad_inches = 0)
        plt.clf()
        plt.close()
        
        # NOTES:
        #   convert matrix into compact form using squareform()
        #   "complete" = Farthest Point Algorithm or Voor Hees Algorithm
        Z = linkage(distance.squareform(distance_matrix_np), method="complete")
        
        font = {'size'   : 10} 
        plt.rc('font', **font)
        fig, ax = plt.subplots()
        
        cluster_threshold = 0.25
        dendrogram(Z, ax=ax, labels=sorted_apps, orientation="right", color_threshold=cluster_threshold)
        ax.vlines([cluster_threshold], *ax.get_ylim(), colors='black', linewidth=1, linestyle='--')
        plt.xlabel("Hamming Distance")
        plt.ylabel("App Category: App Name")
        fig.tight_layout()
        plt.savefig("app-event-similarity-hamming-dendrogram.pdf", bbox_inches='tight', pad_inches = 0)
        plt.clf()
        plt.close()

        ## PART 3: SimRank distance matrix + dendrogram
        S, nodes = simrank(G)
        # df_sim_tmp is a placeholder structure so that we can use it to reference apps more easily later
        # note that dim(df_sim) = |apps + event types| X |apps + event types|
        df_sim_tmp = pd.DataFrame(S, index = nodes, columns = nodes)
        
        distance_matrix_sim_np = np.zeros((len(sorted_apps), len(sorted_apps)))
        for i in range(0, len(sorted_apps)):
            for j in range(0, len(sorted_apps)):
                # note that we want 1 - simrank to use this as a distance
                distance_matrix_sim_np[i, j] = 1 - df_sim_tmp.at[sorted_apps[i],sorted_apps[j]]
                distance_matrix_sim_np[j, i] = distance_matrix_sim_np[i, j]
        
        df_sim = pd.DataFrame(distance_matrix_sim_np, index = sorted_apps, columns = sorted_apps)
        df_hamming.to_csv(r'app-event-similarity-simrank.csv')
        
        font = {'size'   : 6} 
        plt.rc('font', **font)
        fig, ax = plt.subplots()
        im = ax.imshow(distance_matrix_sim_np, cmap='gray', norm=matplotlib.colors.Normalize(vmin=0.0, vmax=1.0, clip=False))
        ax.set_xticks(np.arange(len(sorted_apps)))
        ax.set_yticks(np.arange(len(sorted_apps)))
        ax.set_xticklabels(sorted_apps)
        ax.set_yticklabels(sorted_apps)
        plt.setp(ax.get_xticklabels(), rotation=90, ha="right",
                rotation_mode="anchor")
        plt.setp(ax.get_yticklabels(), rotation=45, ha="right",
                rotation_mode="anchor")
        dx = -3/72.; dy = 0/72. 
        offset = matplotlib.transforms.ScaledTranslation(dx, dy, fig.dpi_scale_trans)
        for label in ax.xaxis.get_majorticklabels():
            label.set_transform(label.get_transform() + offset)
        plt.xlabel("App Category: App Name")
        plt.ylabel("App Category: App Name")
        fig.tight_layout()
        plt.savefig("app-event-similarity-simrank.pdf", bbox_inches='tight', pad_inches = 0)
        plt.clf()
        plt.close()

        Z_sim = linkage(distance.squareform(distance_matrix_sim_np), method="complete")
        
        font = {'size'   : 10} 
        plt.rc('font', **font)
        fig, ax = plt.subplots(figsize=(6, 5))
        
        cluster_threshold = 1.0
        dendrogram(Z_sim, ax=ax, labels=sorted_apps, orientation="right", color_threshold=cluster_threshold)
        ax.vlines([cluster_threshold], *ax.get_ylim(), colors='black', linewidth=1, linestyle='--')
        plt.xlabel("SimRank Distance")
        plt.ylabel("App Category: App Name")
        fig.tight_layout()
        plt.savefig("app-event-similarity-simrank-dendrogram.pdf", bbox_inches='tight', pad_inches = 0)
        plt.clf()
        plt.close()

        ## PART 4: Per-cluster union membership comparison
        
        # get clusters
        # note that cluster_assignments list has same order as sorted_apps
        cluster_assignments = fcluster(Z_sim,cluster_threshold,'distance')
        cluster_ids = set(cluster_assignments)
        num_clusters = len(cluster_ids)
        
        # get intra-clsuter union
        print "Distance threshold for cluster split: %s" % cluster_threshold
        print "Number of resulting clusters: %s" % num_clusters
        print ""
        for cluster_id in cluster_ids:
            print "Cluster %s" % cluster_id
            event_type_union = set()
            apps_in_cluster = []
            
            # step 1: iterate through each app to 1) determine if part of cluster and 2) form union
            for i in range(0, len(sorted_apps)):
                if cluster_assignments[i] == cluster_id:
                    app = sorted_apps[i]
                    apps_in_cluster.append(app)
                    event_type_union = event_type_union.union(apps[app])
                    
            # step 2: iterate again through each app to find difference from union
            # as well as whether app handles that kind of event anyway
            #print "Cluster's union of event types: %s" % event_type_union
            for app in apps_in_cluster:
                print "  App: '%s'" % app
                missing_event_types = event_type_union.difference(apps[app])
                print "    Missing event types (relative to cluster's union + event kind(s) already handled):"
                # get event kinds that this app handles
                event_kinds = set()
                for event_type in apps[app]:
                    event_kinds.add(get_event_kind(event_type))
                for missing in missing_event_types:
                    for event_kind in event_kinds:
                        if missing.startswith(event_kind):
                            print "      %s" % missing
                    

if __name__ == '__main__':
    main()
