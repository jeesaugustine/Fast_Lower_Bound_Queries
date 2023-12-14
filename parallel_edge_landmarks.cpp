#include <cstdio>
#include <algorithm>
#include <map>
#include <list>
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <set>
#include <boost/heap/pairing_heap.hpp>
#include <ctime>
#include <cstdlib>
#include <boost/math/constants/constants.hpp>
#include <chrono>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/erdos_renyi_generator.hpp>
#include <boost/random/linear_congruential.hpp>
#include <utility>
#include <random>
#include <cmath>
#include <thread>
#include <unordered_map>

#include "mpi.h"

const int DEBUG = 0;
const auto processor_count = std::thread::hardware_concurrency();

using namespace std;
int process_rank, size_of_comm;

struct sps
{
    pair<unsigned int, double> data;
    sps(unsigned int node, double dist)
    {
        data = make_pair(node, dist);
    }

    bool operator<(sps const &sps2) const
    {
        return data.second > sps2.data.second;
    }
};

typedef struct{
    unsigned int start, end;
    double length;
} edge_info;

struct VertexProperties
{
    unsigned int index;
};

typedef boost::adjacency_list<boost::vecS, boost::listS, boost::undirectedS, VertexProperties> Graph;
typedef boost::erdos_renyi_iterator<boost::minstd_rand, Graph> ERGen;

vector<double> *Dijkstra(map<unsigned int, map<unsigned int, double>*> * edge_map,
                        unsigned int source, double threshold = 1.)
{
    unsigned int nodes = edge_map->size();
    vector<bool> visited(nodes, false);
    visited.at(source) = true;
    boost::heap::pairing_heap<sps> H;
    // vector<boost::heap::detail::node_handle<boost::heap::detail::heap_node<sps, false>*, boost::heap::detail::make_pairing_heap_base<sps, boost::parameter::aux::empty_arg_list>::type, sps&>> handles;
    vector<boost::heap::pairing_heap<sps>::handle_type> handles;
    vector<double> *sp = new vector<double>(edge_map->size(), 1.);
    sp->at(source) = 0.;
    for (unsigned int j = 0; j < nodes; ++j)
    {
        // handles.push_back((boost::heap::detail::node_handle<boost::heap::detail::heap_node<sps, false>*, boost::heap::detail::make_pairing_heap_base<sps, boost::parameter::aux::empty_arg_list>::type, sps&>)NULL);
        handles.push_back((boost::heap::pairing_heap<sps>::handle_type)NULL);
    }
    for (map<unsigned int, double>::iterator it = edge_map->find(source)->second->begin();
         it != edge_map->find(source)->second->end(); ++it)
    {
        handles.at(it->first) = H.push(sps(it->first, it->second));
    }

    while (!H.empty() && H.top().data.second < 1.)
    {
        unsigned int dest = H.top().data.first;
        double dist = H.top().data.second;
        H.pop();
        sp->at(dest) = dist;
        visited.at(dest) = true;
        for (map<unsigned int, double>::iterator it = edge_map->find(dest)->second->begin();
         it != edge_map->find(dest)->second->end(); ++it)
        {
            unsigned int neighbour = it->first;
            if (visited.at(neighbour))
            {
                continue;
            }
            double total = it->second + dist;
            if (handles.at(neighbour) == (boost::heap::pairing_heap<sps>::handle_type)NULL)
            {
                handles.at(neighbour) = H.push(sps(neighbour, total));
            }
            else if (handles.at(neighbour).node_->value.data.second > total)
            {
                H.increase(handles.at(neighbour), sps(neighbour, total));
            }
        }
    }
    return sp;
}
class EdgeLandMark
{
private:
    map<unsigned int, map<unsigned int, double>*>* edge_map;
    unsigned int no_nodes;
    unsigned int no_landmarks;
    unsigned int no_samples;
    unordered_map<int, vector<double> *> sp_map;
    map<pair<unsigned int, unsigned int>, double> landmarks;
    set<int> landmark_vertices;
    unordered_map<unsigned int, edge_info> edge_loc_rev_map;
    unsigned int edge_size;
    vector<unsigned int> *lookup_interval;

public:
    EdgeLandMark(map<unsigned int, map<unsigned int, double>*>* edge_map, unsigned int n_nodes, unsigned int k, unsigned int sampling_size)
    {
        cout << "No nodes : " << n_nodes << endl << "No landmarks : " << k << endl << "Samples : " << sampling_size << endl;
        no_nodes = n_nodes;
        no_landmarks = k;
        no_samples = sampling_size;
        this->edge_map = edge_map;
        edge_size = 0;
        for(unsigned int i=0; i < no_nodes; ++i) {
            for(auto it=edge_map->find(i)->second->begin(); it != edge_map->find(i)->second->end(); ++it) {
                if(i >= it->first) {
                    continue;
                }
                edge_loc_rev_map.insert({edge_size, edge_info{i, it->first, it->second}});
                edge_size++;
            }
        }
        std::cout << "Edge size " << edge_size << std::endl;
    }

    ~EdgeLandMark()
    {
        for (auto it = this->sp_map.begin(); it != this->sp_map.end(); ++it)
        {
            delete it->second;
        }
    }

    void get_landmarks()
    {
        while (landmarks.size() != no_landmarks)
        {
            if(process_rank == 0 && landmarks.size() > 0) {
                cout << "Selected " << landmarks.size() << " number of landmarks" << endl;
            }
            vector<double> contributions;
            contributions.resize(edge_size);
            for (unsigned int i = 0; i < no_samples; ++i)
            {
                unsigned int u = rand() % this->no_nodes;
                unsigned int v = rand() % this->no_nodes;
                while(u != v && (edge_map->find(min(u, v))->second->find(max(u, v)) != edge_map->find(min(u, v))->second->end())) {
                    u = rand() % this->no_nodes;
                    v = rand() % this->no_nodes;
                }
                if(! sp_map.contains(u)) {
                    sp_map.insert({u, Dijkstra(edge_map, u)});
                }

                if(! sp_map.contains(v)) {
                    sp_map.insert({v, Dijkstra(edge_map, v)});
                }
                double lb_landmarks = this->lookup(u, v);
                unsigned int index_counter = 0;

                for (unsigned index_i = 0; index_i < no_nodes; ++index_i)
                {
                    unsigned int node_x = index_i;

                    for (map<unsigned int, double>::iterator it = edge_map->find(index_i)->second->begin(); it != edge_map->find(index_i)->second->end(); ++it)
                    {
                        if (it->first <= index_i)
                        {
                            continue;
                        }
                        unsigned int node_y = it->first;
                        pair<unsigned int, unsigned int> pair_xy = make_pair(node_x, node_y);
                        if (landmarks.find(pair_xy) != landmarks.end())
                        {
                            ++index_counter;
                            continue;
                        }

                        // Compule LB
                        double edge_len_xy = it->second;
                        vector<double>* dij_u = sp_map.find(u)->second;
                        vector<double>* dij_v = sp_map.find(v)->second;
                        double ux = dij_u->at(node_x), uy = dij_u->at(node_y);
                        double vx = dij_v->at(node_x), vy = dij_v->at(node_y);
                        double lb_edge = 0.0;
                        lb_edge = max({lb_edge, edge_len_xy - ux - vy, edge_len_xy - uy - vx});

                        // If current LB is better than Landmarks update contributions
                        if (lb_edge > lb_landmarks)
                        {
                            // unsigned int loc = edge_loc_map.find(node_x)->second.find(node_y)->second;
                            // contributions.at(loc) += lb_edge - lb_landmarks;
                            contributions.at(index_counter) += lb_edge - lb_landmarks;
                        }
                        ++index_counter;
                    }
                }
            }
            
            std::cout << "Reached collate step " << edge_size <<  " " << process_rank <<  std::endl;
            
            vector<double> contributions_cumulative;
            contributions_cumulative.resize(edge_size);
            MPI_Reduce(contributions.data(), contributions_cumulative.data(), edge_size, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);

            edge_info best_edge;

            if(process_rank == 0) {
                // Only perform cumlative computation on root
                unsigned int best_index = 0;
                for(unsigned int index_contrib = 1; index_contrib < edge_size; ++index_contrib) {
                    if(contributions_cumulative.at(index_contrib) > contributions_cumulative.at(best_index)) {
                        best_index = index_contrib;
                    }
                }
                if(contributions_cumulative.at(best_index) == 0.0) {
                    std::cout << "Something wrong here" << std::endl;
                }

                // Send best_index from 0 to all nodes
                MPI_Bcast(&best_index, 1, MPI_INT, 0, MPI_COMM_WORLD);
                best_edge = edge_loc_rev_map.at(best_index);
                
                pair<unsigned int, unsigned int> pair_out = make_pair(best_edge.start, best_edge.end);
                landmarks.emplace(pair_out, best_edge.length);
                std::cout << "Adding " << best_edge.start << " and " << best_edge.end << " into landmarks." << endl;
            } else {
                unsigned int best_index;
                // Receive best_index from 0
                MPI_Bcast(&best_index, 1, MPI_INT, 0, MPI_COMM_WORLD);

                best_edge = edge_loc_rev_map.at(best_index);
                
                pair<unsigned int, unsigned int> pair_out = make_pair(best_edge.start, best_edge.end);
                landmarks.emplace(pair_out, best_edge.length);
            }
            if(! sp_map.contains(best_edge.start)) {
                sp_map.insert({best_edge.start, Dijkstra(edge_map, best_edge.start)});
            }

            if(! sp_map.contains(best_edge.end)) {
                sp_map.insert({best_edge.end, Dijkstra(edge_map, best_edge.end)});
            }

            landmark_vertices.insert(best_edge.start);
            landmark_vertices.insert(best_edge.end);

        }
    }

    void cleanup_sp() {
        auto sp_map_iter = sp_map.begin();
        // Clean up code for unwanted Shortest paths
        while(sp_map_iter != sp_map.end())
        {
            // Cleanup SP for all paths for not root processor nodes
            // Cleanup SP for paths on root that are not landmarks
            if (!landmark_vertices.contains(sp_map_iter->first))
            {
                delete sp_map_iter->second;
                sp_map_iter = sp_map.erase(sp_map_iter);
            } else {
                ++sp_map_iter;
            }
        }
    }

    double lookup(unsigned int u, unsigned int v)
    {
        double lb_landmarks = 0.0;
        for (auto it = landmarks.begin(); it != landmarks.end(); ++it)
        {
            unsigned int x = it->first.first, y = it->first.second;
            double edge_len_landmark = it->second;
            vector<double> *dij_x = sp_map.find(x)->second;
            vector<double> *dij_y = sp_map.find(y)->second;
            double ux = dij_x->at(u), uy = dij_y->at(u);
            double vx = dij_x->at(v), vy = dij_y->at(v);
            lb_landmarks = max({lb_landmarks, edge_len_landmark - ux - vy, edge_len_landmark - uy - vx});
        }
        return lb_landmarks;
    }

    void set_lookup_vector(vector<unsigned int> *lookup_interval) {
        this->lookup_interval = lookup_interval;
    }

    vector<double>* lookup_vector(unsigned int u, unsigned int v)
    {
        vector<double>* lb_landmarks = new vector<double>();
        lb_landmarks->reserve(lookup_interval->size());
        unsigned int counter = 0;
        unsigned int iter_lookup=0;
        lb_landmarks->at(0) = 0.;
        for (auto it = landmarks.begin(); it != landmarks.end(); ++it) {
            unsigned int x = it->first.first, y = it->first.second;
            double edge_len_landmark = it->second;
            vector<double> *dij_x = sp_map.find(x)->second;
            vector<double> *dij_y = sp_map.find(y)->second;
            double ux = dij_x->at(u), uy = dij_y->at(u);
            double vx = dij_x->at(v), vy = dij_y->at(v);
            lb_landmarks->at(iter_lookup) = max({lb_landmarks->at(iter_lookup), edge_len_landmark - ux - vy, edge_len_landmark - uy - vx});
            ++counter;
            if(counter == lookup_interval->at(iter_lookup)) {
                ++iter_lookup;
                if(counter != landmarks.size()) {
                    lb_landmarks->at(iter_lookup) = lb_landmarks->at(iter_lookup-1);
                }
            }
        }
        ++iter_lookup;
        return lb_landmarks;
    }
};

void clean_up_edge_map(map<unsigned int, map<unsigned int, double>*>* edge_map) {
    for (auto it = edge_map->begin(); it != edge_map->end(); ++it) {
        delete it->second;
    }
    delete edge_map;
}

map<unsigned int, map<unsigned int, double>*>* read_edge_list_from_file(std::string filename, unsigned int &nodes, unsigned int &edges) {
    map<unsigned int, map<unsigned int, double>*>* edge_map = new map<unsigned int, map<unsigned int, double>*>();
    std::ifstream inp_file (filename);
    if (inp_file.is_open()) {
        inp_file >> nodes;

        for(unsigned int i=0; i< nodes; ++i) {
            edge_map->insert({i, new map<unsigned int, double>()});
        }

        unsigned int u, v;
        double dist;
        edges = 0;
        while (inp_file >> u >> v >> dist) {
            edge_map->find(u)->second->insert({v, dist});
            edge_map->find(v)->second->insert({u, dist});
            ++edges;
        }

        inp_file.close();
    }
    std::cout << "Edge count is : " << edges << std::endl;
    return edge_map;
}

double lb_get_exact(map<unsigned int, map<unsigned int, double>*>* edge_map, unsigned int nodes, unsigned int u, unsigned int v) {
    double lb_val = 0.;
    if(u != v) {
        vector<double> *dij_u = Dijkstra(edge_map, u);
        vector<double> *dij_v = Dijkstra(edge_map, v);
        for(unsigned int i=0; i<nodes; ++i) {
            for(auto it=edge_map->find(i)->second->upper_bound(i); it != edge_map->find(i)->second->end(); ++it) {
                // Edge is (i, it->first) with edge length it->second
                unsigned int j = it->first;
                double edge_length = it->second;
                double iu = dij_u->at(i), ju = dij_u->at(j);
                double iv = dij_v->at(i), jv = dij_v->at(j);
                lb_val = max({lb_val, edge_length - iu - jv, edge_length - iv - ju});
            }
        }
    }
    return lb_val;
}

double trisearch(map<unsigned int, map<unsigned int, double>*>* edge_map, unsigned int u, unsigned int v) {
    double lb_val = 0.;
    if(u != v) {
        map<unsigned int, double>::iterator iter_u = edge_map->find(u)->second->begin();
        map<unsigned int, double>::iterator iter_v = edge_map->find(v)->second->begin();
        while(iter_u != edge_map->find(u)->second->end() && iter_v != edge_map->find(v)->second->end()) {
            if(iter_u->first == iter_v->first) {
                lb_val = max(lb_val, max(iter_u->second, iter_v->second)-min(iter_u->second, iter_v->second));
                ++iter_u;
                ++iter_v;
            } else if(iter_u->first < iter_v->first) {
                ++iter_u;
            } else {
                ++iter_v;
            }
        }
    }
    return lb_val;
}

int main(int argc, char** argv){
    MPI_Init(&argc, &argv);
    MPI_Comm_size(MPI_COMM_WORLD, &size_of_comm);
    MPI_Comm_rank(MPI_COMM_WORLD, &process_rank);
    unsigned int init = time(NULL);
    unsigned int nodes, k = 100, sampling_size = 54000, edges;
    unsigned int error_samples = 500;
    std::string filename;
    cout << "This program can be run with following options" << endl;
    cout << "./edge_landmarks <filename> <size of landmarks> <number of samples> [random seed]" << endl;
    cout << "filename - Filename of graph" << endl;
    cout << "size of landmarks - positive integer" << endl;
    cout << "number of samples - positive integer" << endl;
    cout << "samples to compute error  - positive integer" << endl;

    // Error case
    if(argc < 3) {
        std::cout << "Please provide enough arguments" << std::endl;
        MPI_Finalize();
        return 0;
    }
    filename = argv[1];
    k = stoi(argv[2]);
    sampling_size = stoi(argv[3]);

    // Set random seed if specified
    if (argc > 4)
    {
        error_samples = stoi(argv[4]);
    }

    error_samples = ceil(error_samples/size_of_comm);

    // Initialize with random seed
    unsigned int *seed_arr = new unsigned int[size_of_comm];
    if(process_rank == 0) {
        srand(init);
        for(unsigned int i=0; i< size_of_comm; ++i) {
            seed_arr[i] = rand();
        }
    }
    MPI_Scatter(seed_arr, 1, MPI_UNSIGNED, &init, 1, MPI_INT, 0, MPI_COMM_WORLD);
    srand(init);
    delete seed_arr;

    map<unsigned int, map<unsigned int, double>*> *edge_map = read_edge_list_from_file(filename, nodes, edges);
    

    auto start_lb_elm = chrono::high_resolution_clock::now();
    EdgeLandMark *elm = new EdgeLandMark(edge_map, nodes, k, sampling_size);
    std::cout << "Sampling edges" << endl;

    // Get the landmarks parallely using MPI
    elm->get_landmarks();

    // Compute the total time consumed
    auto stop_lb_elm = chrono::high_resolution_clock::now();
    auto duration_lb_elm = chrono::duration_cast<chrono::microseconds>(stop_lb_elm - start_lb_elm);
    if(process_rank == 0) {
        std::cout << "Duration ELM LB:" << duration_lb_elm.count() / 1000000.0 << endl;   
    }

    // Cleanup all other SPs
    elm->cleanup_sp();

    std::cout << "Cleanup complete" << std::endl;

    double error_tot_our = 0., error_tot_tri = 0.;
    double error_tot_our_perc = 0., error_tot_tri_perc = 0.;
    for(unsigned int i=0; i < error_samples; ++i) {
        unsigned int u = rand() % nodes;
        unsigned int v = rand() % nodes;
        while(u != v && (edge_map->find(min(u, v))->second->find(max(u, v)) != edge_map->find(min(u, v))->second->end())) {
            u = rand() % nodes;
            v = rand() % nodes;
        }

        double lb_our = elm->lookup(u, v);
        double lb_exact = lb_get_exact(edge_map, nodes, u, v);
        double lb_tri = trisearch(edge_map, u, v);

        error_tot_our += (lb_exact - lb_our);
        error_tot_tri += (lb_exact - lb_tri);
        if(lb_exact != 0) {
            error_tot_our_perc += (1-(lb_our/lb_exact));
            error_tot_tri_perc += (1-(lb_tri/lb_exact));
        }
        // std::cout << "Edge is (" << u << "," << v << ")" << std::endl;
        // std::cout << "Our LB is : " << elm->lookup(u, v) << std::endl;
        // std::cout << "LB exact is : " << lb_get_exact(edge_map, nodes, u, v) << std::endl;
        // std::cout << "Trisearch is : " << trisearch(edge_map, u, v) << std::endl;
        if(lb_our > lb_exact && lb_our - lb_exact > 0.0001) {
            std::cout << "Error!" << lb_our << " " << lb_exact << std::endl;
        }
    }

    double global_tot_error, global_tot_tri;
    double global_tot_perc_error, global_tot_perc_tri;

    std::cout << "Error local ours " << error_tot_our << " " << error_tot_our_perc << std::endl;
    std::cout << "Error local Tri " << error_tot_tri << " " << error_tot_tri_perc << std::endl;

    MPI_Reduce(&error_tot_our, &global_tot_error, 1, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);
    MPI_Reduce(&error_tot_our_perc, &global_tot_perc_error, 1, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);
    MPI_Reduce(&error_tot_tri, &global_tot_tri, 1, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);
    MPI_Reduce(&error_tot_tri_perc, &global_tot_perc_tri, 1, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);
    
    if(process_rank == 0) {
        std::cout << "Our error is " << global_tot_error << " "  << global_tot_perc_error << std::endl;
        std::cout << "Tri error is " << global_tot_tri << " "  << global_tot_perc_tri << std::endl;
    }

    // Cleanup edge_map as a final step
    clean_up_edge_map(edge_map);

    MPI_Finalize();
    return 0;
}
