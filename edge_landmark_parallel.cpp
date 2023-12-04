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

vector<double> *Dijkstra(vector<vector<pair<unsigned int, double>> *> *adj_lst,
                        unsigned int source, double threshold = 1.)
{
    unsigned int nodes = adj_lst->size();
    vector<bool> visited(nodes, false);
    visited.at(source) = true;
    boost::heap::pairing_heap<sps> H;
    // vector<boost::heap::detail::node_handle<boost::heap::detail::heap_node<sps, false>*, boost::heap::detail::make_pairing_heap_base<sps, boost::parameter::aux::empty_arg_list>::type, sps&>> handles;
    vector<boost::heap::pairing_heap<sps>::handle_type> handles;
    vector<double> *sp = new vector<double>(adj_lst->size(), 1.);
    sp->at(source) = 0.;
    for (unsigned int j = 0; j < nodes; ++j)
    {
        // handles.push_back((boost::heap::detail::node_handle<boost::heap::detail::heap_node<sps, false>*, boost::heap::detail::make_pairing_heap_base<sps, boost::parameter::aux::empty_arg_list>::type, sps&>)NULL);
        handles.push_back((boost::heap::pairing_heap<sps>::handle_type)NULL);
    }
    for (vector<pair<unsigned int, double>>::iterator it = adj_lst->at(source)->begin();
         it != adj_lst->at(source)->end(); ++it)
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
        for (vector<pair<unsigned int, double>>::iterator it = adj_lst->at(dest)->begin();
             it != adj_lst->at(dest)->end(); ++it)
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
    vector<vector<pair<unsigned int, double>> *> *adj_list;
    map<unsigned int, map<unsigned int, double>> edge_map;
    unsigned int no_nodes;
    unsigned int no_landmarks;
    unsigned int no_samples;
    unordered_map<int, vector<double> *> sp_map;
    map<pair<unsigned int, unsigned int>, double> landmarks;
    set<int> landmark_vertices;
    // map<unsigned int, map<unsigned int, unsigned int>> edge_loc_map;
    unordered_map<unsigned int, edge_info> edge_loc_rev_map;
    unsigned int edge_size;
    vector<unsigned int> *lookup_interval;

public:
    EdgeLandMark(vector<vector<pair<unsigned int, double>> *> *adj_list, unsigned int n_nodes, unsigned int k, unsigned int sampling_size)
    {
        cout << "No nodes : " << n_nodes << endl << "No landmarks : " << k << endl << "Samples : " << sampling_size << endl;
        no_nodes = n_nodes;
        for(unsigned int i=0; i< no_nodes; ++i) {
            map<unsigned int, double> t;
            edge_map.insert({i, t});
        }
        no_landmarks = k;
        no_samples = sampling_size;
        this->adj_list = adj_list;
        edge_size = 0;
        for(unsigned int i=0; i < no_nodes; ++i) {
            for(auto it=adj_list->at(i)->begin(); it != adj_list->at(i)->end(); ++it) {
                if(i >= it->first) {
                    continue;
                }
                // if(! edge_loc_map.contains(i)) {
                //     map<unsigned int, unsigned int> temp;
                //     edge_loc_map.insert({i, temp});
                // }
                // edge_loc_map.find(i)->second.insert({it->first, edge_size});
                edge_loc_rev_map.insert({edge_size, edge_info{i, it->first, it->second}});
                edge_map.find(i)->second.insert({it->first, it->second});
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
                while(u != v && (edge_map.find(min(u, v))->second.find(max(u, v)) != edge_map.find(min(u, v))->second.end())) {
                    u = rand() % this->no_nodes;
                    v = rand() % this->no_nodes;
                }
                if(! sp_map.contains(u)) {
                    sp_map.insert({u, Dijkstra(adj_list, u)});
                }

                if(! sp_map.contains(v)) {
                    sp_map.insert({v, Dijkstra(adj_list, v)});
                }
                double lb_landmarks = this->lookup(u, v);
                unsigned int index_counter = 0;

                for (unsigned index_i = 0; index_i < no_nodes; ++index_i)
                {
                    unsigned int node_x = index_i;

                    for (vector<pair<unsigned int, double>>::iterator it = adj_list->at(index_i)->begin(); it != adj_list->at(index_i)->end(); ++it)
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
            MPI_Reduce(contributions.data(), contributions_cumulative.data(), edge_size, MPI_FLOAT, MPI_SUM, 0, MPI_COMM_WORLD);

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
                sp_map.insert({best_edge.start, Dijkstra(adj_list, best_edge.start)});
            }

            if(! sp_map.contains(best_edge.end)) {
                sp_map.insert({best_edge.end, Dijkstra(adj_list, best_edge.end)});
            }

            landmark_vertices.insert(best_edge.start);
            landmark_vertices.insert(best_edge.end);

        }
    }

    vector<double> * snatch_sp(unsigned int node) {
        if(sp_map.contains(node)) {
            vector<double> *sp_ptr = sp_map.find(node)->second;
            sp_map.erase(node);
            return sp_ptr;
        }
        else {
            return nullptr;
        }
    }

    vector<double> *get_sp_vector(unsigned int node) {
        if(sp_map.contains(node)) {
            return sp_map.find(node)->second;
        } else {
            return nullptr;
        }
    }

    bool has_sp(unsigned int node) {
        return sp_map.contains(node);
    }

    bool is_landmark(unsigned int node) {
        return landmark_vertices.contains(node);
    }

    void cleanup_sp() {
        // Clean up code for unwanted Shortest paths
        for (auto sp_map_iter = sp_map.begin(); sp_map_iter != sp_map.end(); ++sp_map_iter)
        {
            // Cleanup SP for all paths for not root processor nodes
            // Cleanup SP for paths on root that are not landmarks
            if (!landmark_vertices.contains(sp_map_iter->first) || process_rank != 0)
            {
                delete sp_map.find(sp_map_iter->first)->second;
                sp_map.erase(sp_map_iter->first);
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

void clean_up_adj_list(vector<vector<pair<unsigned int, double>> *> *adj_lst)
{
    unsigned int adj_lst_size = adj_lst->size();
    while (adj_lst_size-- > 0)
    {
        delete adj_lst->at(adj_lst_size);
    }
    delete adj_lst;
}

vector<vector<pair<unsigned int, double>> *> * read_adj_list_file(std::string filename, unsigned int &nodes, unsigned int &edges) {
    vector<vector<pair<unsigned int, double>> *> *adj_lst = new vector<vector<pair<unsigned int, double>> *>();

    std::ifstream inp_file (filename);
    if (inp_file.is_open())
    {
        inp_file >> nodes;

        for(unsigned int i=0; i< nodes; ++i) {
            adj_lst->push_back(new vector<pair<unsigned int, double>>());
        }

        // unsigned int edges;

        // inp_file >> edges;
        // unsigned int node_u, node_v;
        // double edge_length;
        // for(unsigned int i=0; i<edges; ++i) {
        //     inp_file >> node_u >> node_v >> edge_length;
        //     adj_lst->at(min(node_u, node_v))->push_back(make_pair(max(node_u, node_v), edge_length));
        // }

        unsigned int u, v;
        double dist;
        edges = 0;
        while (inp_file >> u >> v >> dist) {
            adj_lst->at(u)->push_back(make_pair(v, dist));
            adj_lst->at(v)->push_back(make_pair(u, dist));
            ++edges;
            unsigned int u1 = min(u, v);
            unsigned int v1 = max(u, v);
        }

        inp_file.close();
    }
    return adj_lst;
}    

/*
snatch_or_compute: If the shortest path is already stored in elm data structure, then it can be snatched if
    the processor is not the roor processor or it is not part of landmarks.
*/
std::vector<double> * snatch_or_compute(vector<vector<pair<unsigned int, double>> *> *adj_lst, EdgeLandMark *elm, unsigned int node) {
    std::vector<double> *dij;

    if(elm->has_sp(node)) {
        if(process_rank != 0 || !elm->is_landmark(node)) {
            dij = elm->snatch_sp(node);
        } else {
            dij = new std::vector<double>();
            std::vector<double> *sp_tmp = elm->get_sp_vector(node);
            for(unsigned int i=0; i < sp_tmp->size(); ++i) {
                dij->push_back(sp_tmp->at(i));
            }
        }
    } else {
        dij = Dijkstra(adj_lst, node);
    }

    return dij;
}

int main(int argc, char** argv){
    int distro_Array[4] = {39, 72, 129, 42};
    int scattered_Data;

    MPI_Init(&argc, &argv);
    MPI_Comm_size(MPI_COMM_WORLD, &size_of_comm);
    MPI_Comm_rank(MPI_COMM_WORLD, &process_rank);
    unsigned int init = time(NULL);
    unsigned int nodes, k = 100, sampling_size = 54000, edges;
    std::string filename;
    cout << "This program can be run with following options" << endl;
    cout << "./edge_landmarks <filename> <size of landmarks> <number of samples> [random seed]" << endl;
    cout << "filename - Filename of graph" << endl;
    cout << "size of landmarks - positive integer" << endl;
    cout << "number of samples - positive integer" << endl;

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
        init = stoi(argv[4]);
    }

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

    vector<vector<pair<unsigned int, double>> *> * adj_lst = read_adj_list_file(filename, nodes, edges);
    

    auto start_lb_elm = chrono::high_resolution_clock::now();
    EdgeLandMark *elm = new EdgeLandMark(adj_lst, nodes, k, sampling_size);
    std::cout << "Sampling edges" << endl;

    // Get the landmarks parallely using MPI
    elm->get_landmarks();

    // Compute the total time consumed
    auto stop_lb_elm = chrono::high_resolution_clock::now();
    auto duration_lb_elm = chrono::duration_cast<chrono::microseconds>(stop_lb_elm - start_lb_elm);
    if(process_rank == 0) {
        std::cout << "Duration ELM LB:" << duration_lb_elm.count() / 1000000.0 << endl;   
    }

    // Compute the exact LB values in parallel
    // 1. Distribute the m edges among the different processors (m_1, m_2, ..., m_p)
    // 2. For every vertex v_j that lies in processor P_i compute the SP from v_j to all other vertices
    // 3. For every incoming vertex v_j compute the LB between v_j to all other vertices using m_i edges as the longest edges
    // 4. Merge the various LBs using min operation and compute the score using different measures
    unordered_map<int, vector<double> *>* sp_map_local = new unordered_map<int, vector<double> *>();


    // 1. Distribute the m edges among the different processors (m_1, m_2, ..., m_p)
    // 2. For every vertex v_j that lies in processor P_i compute the SP from v_j to all other vertices


    // Get Shortest paths
    unsigned int jump = floor(edges / size_of_comm), remaining = edges % size_of_comm, start, end;
    if(remaining > process_rank) {
        start = process_rank * (jump + 1);
        end = start + jump + 1;
    } else {
        start = process_rank * jump + remaining;
        end = start + jump;
    }

    unsigned int count = 0, iter_index=0; 
    for(iter_index=0; iter_index < nodes; ++iter_index) {
        if(count + adj_lst->at(iter_index)->size() <= start) {
            count += adj_lst->at(iter_index)->size();
        } else {
            break;
        }
    }

    unsigned int inner_index = start-count;

    // Store inner_index and iter_index for later computations
    unsigned int edges_inner_index = inner_index, edges_iter_index = iter_index;

    count = start;
    while(count < end) {
        if(!sp_map_local->contains(iter_index)) {
            sp_map_local->insert({iter_index, snatch_or_compute(adj_lst, elm, iter_index)});
        }
        for(; count < end && inner_index < adj_lst->at(iter_index)->size(); ++inner_index) {
            if(!sp_map_local->contains(adj_lst->at(iter_index)->at(iter_index).first)) {
                sp_map_local->insert({iter_index, snatch_or_compute(adj_lst, elm, iter_index)});
            }
            ++count;
        }
        ++iter_index;
        inner_index = 0;
    }
    // Cleanup all other SPs
    elm->cleanup_sp();

    std::cout << "Cleanup complete" << std::endl;

    double relative = 0., rmse = 0.;
    for(unsigned int i=0; i<nodes; ++i) {
        std::vector<double> lb_values;
        unsigned int lb_size = nodes-1-i;
        lb_values.reserve(lb_size);

        // 3. For every incoming vertex v_j compute the LB between v_j to all other vertices using m_i edges as the longest edges
        for(unsigned int j=i+1; j<nodes; ++j) {
            unsigned int inner_index = edges_inner_index, iter_index = edges_iter_index;
            count = start;
            lb_values[j-i-1] = 0.0;
            while(count < end) {
                for(; count < end && inner_index < adj_lst->at(iter_index)->size(); ++inner_index) {
                    double sp_ui = sp_map_local->find(iter_index)->second->at(i), sp_uj = sp_map_local->find(iter_index)->second->at(j); 
                    double sp_vi = sp_map_local->find(inner_index)->second->at(i), sp_vj = sp_map_local->find(inner_index)->second->at(j); 
                    double edge_len = adj_lst->at(iter_index)->at(inner_index).second;
                    lb_values[j-i-1] = max(lb_values[j-i-1], edge_len - sp_ui - sp_vj);
                    lb_values[j-i-1] = max(lb_values[j-i-1], edge_len - sp_uj - sp_vi);
                    ++count;
                }
                ++iter_index;
                inner_index = 0;
            }
        }

        // 4. Merge the various LBs using min operation and compute the score using different measures
        if(process_rank == 0) {
            // MPI_Reduce
            std::vector<double> lb_values_reduced;
            lb_values_reduced.reserve(lb_size);
            MPI_Reduce(&lb_values_reduced, &lb_values, lb_size, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD);
            
            // Compute score in groups
            for(unsigned int k=i+1; k<nodes; ++k) {
                // For varying k use lookup_interval code 
                double lb_value = elm->lookup(i, k);
                relative += (1- (lb_value/lb_values_reduced.at(k-i-1)));
                
                double diff_lb_score = lb_values_reduced.at(k-i-1) - lb_value;
                rmse += diff_lb_score * diff_lb_score;
            }
        }
        else {
            // MPI_Reduce
            MPI_Reduce(&lb_values, &lb_values, lb_size, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD);
        }
    
    }

    clean_up_adj_list(adj_lst);

    MPI_Finalize();
    return 0;
}