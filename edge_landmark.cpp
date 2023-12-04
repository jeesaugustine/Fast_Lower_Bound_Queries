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
#include <set>


const int DEBUG = 0;

using namespace std;
using namespace boost::heap;
using namespace boost;

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

struct min_heap_edge
{
    unsigned int u,v;
    double dist;
    min_heap_edge(unsigned int u, unsigned int v, double dist)
    {
        this->u = u;
        this->v = v;
        this->dist = dist;
    }

    bool operator<(min_heap_edge const &that) const
    {
        return this->dist > that.dist;
    }
};

struct VertexProperties
{
    unsigned int index;
};

class path {
private:
    pair <unsigned int, unsigned int> edge;
    double distance;
public:
    path(unsigned int end_point1, unsigned int end_point2, double dist) {
        if(end_point1 < end_point2){
            edge = make_pair(end_point1, end_point2);
        } else {
            edge = make_pair(end_point2, end_point1);
        }
        distance = dist;
        return;
    }

    virtual ~path(){}

    double get_distance() const {
        return distance;
    }

    pair<unsigned int, unsigned int> get_edge() const {
        return edge;
    }

    void set_distance(double dist) {
        distance = dist;
    }

    bool operator <(const path & pathObj) const    {
        return distance < pathObj.distance;
    }
};

typedef boost::adjacency_list<boost::vecS, boost::listS, boost::undirectedS, VertexProperties> Graph;
typedef boost::erdos_renyi_iterator<boost::minstd_rand, Graph> ERGen;

vector<double> *Dijkstra(vector<list<pair<unsigned int, double>> *> *adj_lst,
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
    for (list<pair<unsigned int, double>>::iterator it = adj_lst->at(source)->begin();
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
        for (list<pair<unsigned int, double>>::iterator it = adj_lst->at(dest)->begin();
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

void compute_lb(vector<list<pair<unsigned int, double>>*>* adj_lst,
        vector<vector<double>*>* adj_mat, vector<vector<double>*>* lb_mat) {
    pairing_heap<path> H;
    unsigned int nodes = adj_lst->size();
    vector<bool> unknown(nodes, true);
    vector<vector<pairing_heap<path>::handle_type>> handles;
    for(unsigned int i = 0; i < nodes; ++i) {
        vector<pairing_heap<path>::handle_type> v;
        for(unsigned int j = 0; j < nodes; ++j) {
            unknown.at(j) = true;
            v.push_back((pairing_heap<path>::handle_type)NULL);
        }
        unknown.at(i) = false;
        for (list<pair<unsigned int, double>>::iterator it=adj_lst->at(i)->begin();
                it != adj_lst->at(i)->end(); ++it) {
            unsigned int end = it->first;
            unknown.at(end) = false;
        }
        for(unsigned int j = 0; j < i; ++j) {
            v.at(j) = handles.at(j).at(i);
        }
        for(unsigned int j = i + 1; j < nodes; ++j) {
            if(unknown.at(j)) {
                v.at(j) = H.push(path(i, j, 0.));
            }
        }
        handles.push_back(v);
    }
    // All paths of length 2
    for(unsigned int i = 0; i < nodes; ++i) {
        auto end = adj_lst->at(i)->end();
        for (auto it=adj_lst->at(i)->begin();it != end; ++it) {
            for(auto it_fwd = std::next(it); it_fwd != end; ++it_fwd) {
                unsigned int end1 = it->first, end2 = it_fwd->first;
                if(adj_mat->at(end1)->at(end2) > -0.1) {
                    continue;
                }
                double val1 = adj_mat->at(i)->at(end1), val2 = adj_mat->at(i)->at(end2);
                double lb_val = abs(val1 - val2);
                //lb_mat->at(end1)->at(end2) = max(lb_val, lb_mat->at(end1)->at(end2));
                if(handles.at(end1).at(end2).node_->value.get_distance() < lb_val) {
                    H.increase(handles.at(end1).at(end2), path(end1, end2, lb_val));
                }
            }
        }
    }
    // Empty heap
    while(H.size() > 0) {
        auto edge = H.top().get_edge();
        double dist = max(H.top().get_distance(), 0.);
        H.pop();
        if(lb_mat->at(edge.first)->at(edge.second) < dist) {
            lb_mat->at(edge.first)->at(edge.second) = dist;
            lb_mat->at(edge.second)->at(edge.first) = dist;
        }
        // Add all neighbours
        if(dist <= 0.) {
            continue;
        }
        for (auto it=adj_lst->at(edge.first)->begin();it != adj_lst->at(edge.first)->end(); ++it) {
            // Update lengths of edges on heap
            unsigned int end_point = it->first;
            unsigned int min_end = min(end_point, edge.second), max_end = max(end_point, edge.second);
            if(adj_mat->at(min_end)->at(max_end) < 0.) {
                double val = dist - it->second;
                if(val > handles.at(min_end).at(max_end).node_->value.get_distance()) {
                    H.increase(handles.at(min_end).at(max_end), path(min_end, max_end, val));
                }
            }
        }
        for (auto it=adj_lst->at(edge.second)->begin();it != adj_lst->at(edge.second)->end(); ++it) {
            // Update lengths of edges on heap
            unsigned int end_point = it->first;
            unsigned int min_end = min(end_point, edge.first), max_end = max(end_point, edge.first);
            if(adj_mat->at(min_end)->at(max_end) < 0.) {
                double val = dist - it->second;
                if(val > handles.at(min_end).at(max_end).node_->value.get_distance()) {
                    H.increase(handles.at(min_end).at(max_end), path(min_end, max_end, val));
                }
            }
        }
    }
}

class TriSearch{
private:
    unsigned int no_nodes;
    vector<map<unsigned int, double>*>* ord_adj_list;
public:
    TriSearch(vector<list<pair<unsigned int, double>> *> *adj_list, unsigned int n_nodes) {
        no_nodes = n_nodes;
        ord_adj_list = new vector<map<unsigned int, double>*>();
        for(unsigned int i = 0; i < no_nodes; ++i)
        {
            ord_adj_list->push_back(new map<unsigned int, double>());
        }
        for (unsigned int i = 0; i < no_nodes; ++i)
        {
            for(auto itr=adj_list->at(i)->begin(); itr != adj_list->at(i)->end(); ++itr) {
                unsigned int j = itr->first;
                double dist = itr->second;
                if(!ord_adj_list->at(i)->contains(j)) {
                    ord_adj_list->at(i)->insert({j, dist});
                    ord_adj_list->at(j)->insert({i, dist});
                }
            }
        }
    }

    ~TriSearch() {
        for(unsigned int i = 0; i < no_nodes; ++i) {
            delete ord_adj_list->at(i);
        }
        delete ord_adj_list;
    }

    double lookup(unsigned int u, unsigned int v) {
        double lb = 0.0;
        auto itr_u=ord_adj_list->at(u)->begin();
        auto itr_v=ord_adj_list->at(v)->begin();
        if(u == v) {
            return lb;
        }
        while( itr_u != ord_adj_list->at(u)->end() && itr_v != ord_adj_list->at(v)->end()) {
            if(itr_u->first == itr_v->first) {
                lb = max(lb, abs(itr_u->second - itr_v->second));
                ++itr_u;
                ++itr_v;
            } else if(itr_u->first < itr_v->first) {
                ++itr_u;
            } else {
                ++itr_v;
            }
        }
        return lb;
    }
};

class EdgeLandMark
{
private:
    vector<list<pair<unsigned int, double>> *> *adj_list;
    unsigned int no_nodes;
    unsigned int no_landmarks;
    unsigned int no_samples;
    vector<vector<double> *> *sp_vector;
    map<pair<unsigned int, unsigned int>, double> *landmarks;
    map<pair<unsigned int, unsigned int>, double> *edges_map;
    set<unsigned int> sps_accessed;

public:
    EdgeLandMark(vector<list<pair<unsigned int, double>> *> *adj_list, unsigned int n_nodes, unsigned int k, unsigned int sampling_size)
    {
        cout << "No nodes : " << n_nodes << endl << "No landmarks : " << k << endl << "Samples : " << sampling_size << endl;
        no_nodes = n_nodes;
        no_landmarks = k;
        no_samples = sampling_size;
        this->adj_list = adj_list;
        store_map();
        sp_vector = new vector<vector<double> *>();
        for (unsigned int i = 0; i < no_nodes; ++i)
        {
            sp_vector->push_back(Dijkstra(adj_list, i));
        }
        landmarks = new map<pair<unsigned int, unsigned int>, double>();
    }

    ~EdgeLandMark()
    {
        if (sp_vector)
        {
            for (auto it = this->sp_vector->begin(); it != this->sp_vector->end(); ++it)
            {
                delete *it;
            }
            delete sp_vector;
        }
        delete landmarks;
        delete edges_map;
    }

    void store_map() {
        // vector<list<pair<unsigned int, double>> *> *adj_list;
        edges_map = new map<pair<unsigned int, unsigned int>, double>();
        for(unsigned int i=0; i< adj_list->size(); ++i) {
            for(auto itr=adj_list->at(i)->begin(); itr != adj_list->at(i)->end(); ++itr) {
                unsigned int j = itr->first;
                double dist = itr->second;
                unsigned int u = min(i, j), v = max(i, j);
                pair<unsigned int, unsigned int> pr = make_pair(i, j);
                if(!edges_map->contains(pr)) {
                    edges_map->insert({pr, dist});
                }
            }
        }
    }

    void large_edge_heuristic() {
        // Min heap
        pairing_heap<min_heap_edge> H;
        for(auto itr = edges_map->begin(); itr != edges_map->end(); ++itr) {
            double dist = itr->second;
            if(H.size() < no_landmarks) {
                H.push(min_heap_edge(itr->first.first, itr->first.second, dist));
            }
            else if(H.size() >= no_landmarks && H.top().dist < dist) {
                H.pop();
                H.push(min_heap_edge(itr->first.first, itr->first.second, dist));
            }
        }
        while(H.size() > 0) {
            min_heap_edge edge = H.top();
            H.pop();
            landmarks->insert({make_pair(edge.u, edge.v), edge.dist});
        }
    }

    void far_away_heuristic() {
        map<pair<unsigned int, unsigned int>, double> distance_map;
        unsigned int last_landmark_u, last_landmark_v;
        while(landmarks->size() != no_landmarks) {
            if(landmarks->size() == 0) {
                for(auto itr = edges_map->begin(); itr != edges_map->end(); ++itr) {
                    if(itr == edges_map->begin()) {
                        landmarks->insert({itr->first, itr->second});
                        last_landmark_u = itr->first.first;
                        last_landmark_v = itr->first.second;
                    } else {
                        distance_map.insert({itr->first, 0.0});
                    }
                }
            } else {
                unsigned int min_u, min_v;
                double min_dist = no_nodes;
                for(auto itr = edges_map->begin(); itr != edges_map->end(); ++itr) {
                    if(landmarks->contains(itr->first)) {
                        continue;
                    }
                    unsigned int x = itr->first.first, y = itr->first.second;
                    distance_map.find(itr->first)->second += min(sp_vector->at(last_landmark_u)->at(x) + sp_vector->at(last_landmark_v)->at(y),
                                                                 sp_vector->at(last_landmark_v)->at(x) + sp_vector->at(last_landmark_u)->at(y));
                    if(distance_map.find(itr->first)->second < min_dist) {
                        min_dist = distance_map.find(itr->first)->second;
                        min_u = x;
                        min_v = y;
                    }
                }
                landmarks->insert({make_pair(min_u, min_v), edges_map->find(make_pair(min_u, min_v))->second});
                distance_map.erase(make_pair(min_u, min_v));
            }
        }
    }

    void get_exact_landmarks() {
        while (landmarks->size() != no_landmarks)
        {
            if(landmarks->size()>0) {
                cout << "Selected " << landmarks->size() << " number of landmarks" << endl;
            }
            double value_out = 0.0;
            unsigned int out_x;
            unsigned int out_y;
            double out_edge_len = 0.0;
            map<pair<unsigned int, unsigned int>, double> contributions;

            
            for (unsigned int i = 0; i < no_nodes; ++i) {
                for (unsigned int j = i+1; j < no_nodes; ++j) {
                    unsigned int u = min(i, j), v = max(i, j);
                    if(edges_map->contains(make_pair(u, v))) {
                        continue;
                    }
                    double lb_landmarks = this->lookup(u, v);
                    
                    for(auto itr = edges_map->begin(); itr != edges_map->end(); ++itr) {
                        unsigned int node_x = itr->first.first, node_y = itr->first.second;
                        pair<unsigned int, unsigned int> pair_xy = make_pair(node_x, node_y);
                        if (landmarks->find(pair_xy) != landmarks->end())
                        {
                            continue;
                        }

                        // Compule LB
                        double edge_len_xy = itr->second;
                        double ux = sp_vector->at(u)->at(node_x), uy = sp_vector->at(u)->at(node_y);
                        double vx = sp_vector->at(v)->at(node_x), vy = sp_vector->at(v)->at(node_y);
                        double lb_edge = 0.0;
                        lb_edge = max({lb_edge, edge_len_xy - ux - vy, edge_len_xy - uy - vx});
                        if (lb_edge > lb_landmarks)
                        {
                            if (contributions.contains(pair_xy))
                            {
                                contributions.insert({pair_xy, 0.0});
                            }
                            contributions[pair_xy] += lb_edge - lb_landmarks;
                            if (value_out < contributions[pair_xy])
                            {
                                value_out = contributions[pair_xy];
                                out_x = node_x;
                                out_y = node_y;
                                out_edge_len = edge_len_xy;
                            }
                        }

                    }

                }
            }
            if (value_out == 0.0)
            {
                cout << "Something wrong here!" << endl;
            }
            else
            {
                pair<unsigned int, unsigned int> pair_out = make_pair(out_x, out_y);
                landmarks->insert({pair_out, out_edge_len});
                cout << "Adding " << out_x << " and " << out_y << " into landmarks." << endl;
            }
        }
    }

    void clean_unwanted_shortest_paths() {
        // Clean up code for unwanted Shortest paths
        for (unsigned int index_i = 0; index_i < no_nodes; ++index_i)
        {
            bool present = false;
            for (auto it = landmarks->begin(); it != landmarks->end(); ++it)
            {
                if (it->first.first == index_i || it->first.second == index_i)
                {
                    // cout << "Skipping clean up of SP : " << index_i << std::endl;
                    present = true;
                    break;
                }
            }
            if (!present)
            {
                delete sp_vector->at(index_i);
                sp_vector->at(index_i) = NULL;
            }
        }
    }

    void get_landmarks()
    {
        while (landmarks->size() != no_landmarks)
        {
            if(landmarks->size()>0) {
                cout << "Selected " << landmarks->size() << " number of landmarks" << endl;
            }
            double value_out = 0.0;
            unsigned int out_x;
            unsigned int out_y;
            double out_edge_len = 0.0;
            map<pair<unsigned int, unsigned int>, double> contributions;
            for (unsigned int i = 0; i < no_samples; ++i)
            {
                unsigned int u = rand() % this->no_nodes;
                unsigned int v = rand() % this->no_nodes;

                // Sample edges that are not known
                while(edges_map->contains(make_pair(min(u,v), max(u,v)))) {
                    u = rand() % this->no_nodes;
                    v = rand() % this->no_nodes;
                }
                sps_accessed.insert(u);
                sps_accessed.insert(v);
                double lb_landmarks = this->lookup(u, v);
                for (unsigned index_i = 0; index_i < no_nodes; ++index_i)
                {
                    unsigned int node_x = index_i;
                    for (list<pair<unsigned int, double>>::iterator it = adj_list->at(index_i)->begin(); it != adj_list->at(index_i)->end(); ++it)
                    {
                        if (it->first <= index_i)
                        {
                            continue;
                        }
                        unsigned int node_y = it->first;
                        pair<unsigned int, unsigned int> pair_xy = make_pair(node_x, node_y);
                        if (landmarks->find(pair_xy) != landmarks->end())
                        {
                            continue;
                        }

                        // Compule LB
                        double edge_len_xy = it->second;
                        double ux = sp_vector->at(u)->at(node_x), uy = sp_vector->at(u)->at(node_y);
                        double vx = sp_vector->at(v)->at(node_x), vy = sp_vector->at(v)->at(node_y);
                        double lb_edge = 0.0;
                        lb_edge = max({lb_edge, edge_len_xy - ux - vy, edge_len_xy - uy - vx});
                        if (lb_edge > lb_landmarks)
                        {
                            if (contributions.find(pair_xy) == contributions.end())
                            {
                                contributions.emplace(pair_xy, 0.0);
                            }
                            contributions[pair_xy] += lb_edge - lb_landmarks;
                            if (value_out < contributions[pair_xy])
                            {
                                value_out = contributions[pair_xy];
                                out_x = node_x;
                                out_y = node_y;
                                out_edge_len = edge_len_xy;
                            }
                        }
                    }
                }
            }
            if (value_out == 0.0)
            {
                cout << "Something wrong here!" << endl;
            }
            else
            {
                pair<unsigned int, unsigned int> pair_out = make_pair(out_x, out_y);
                landmarks->emplace(pair_out, out_edge_len);
                cout << "Adding " << out_x << " and " << out_y << " into landmarks." << endl;
            }
        }
        cout << "Size of SPs run is : " << sps_accessed.size() << endl;
    }

    double lookup(unsigned int u, unsigned int v)
    {
        double lb_landmarks = 0.0;
        for (auto it = landmarks->begin(); it != landmarks->end(); ++it)
        {
            unsigned int x = it->first.first, y = it->first.second;
            double edge_len_landmark = it->second;
            double ux = sp_vector->at(x)->at(u), uy = sp_vector->at(y)->at(u);
            double vx = sp_vector->at(x)->at(v), vy = sp_vector->at(y)->at(v);
            lb_landmarks = max({lb_landmarks, edge_len_landmark - ux - vy, edge_len_landmark - uy - vx});
        }
        return lb_landmarks;
    }

    vector<double>* lookup_multiple(unsigned int u, unsigned int v) {
        vector<double>* lb_vals = new vector<double>();
        double lb_landmarks = 0.0;
        for (auto it = landmarks->begin(); it != landmarks->end(); ++it)
        {
            unsigned int x = it->first.first, y = it->first.second;
            double edge_len_landmark = it->second;
            double ux = sp_vector->at(x)->at(u), uy = sp_vector->at(y)->at(u);
            double vx = sp_vector->at(x)->at(v), vy = sp_vector->at(y)->at(v);
            lb_landmarks = max({lb_landmarks, edge_len_landmark - ux - vy, edge_len_landmark - uy - vx});
            lb_vals->push_back(lb_landmarks);
        }
        return lb_vals;
    }
};

void SashaWang(vector<vector<double> *> *lb, vector<vector<double> *> *ub)
{
    unsigned int nodes = lb->size();
    for (unsigned int k = 0; k < nodes; ++k)
    {
        for (unsigned int j = 0; j < nodes; ++j)
        {
            for (unsigned int i = 0; i < nodes; ++i)
            {
                double max_lb = max(lb->at(i)->at(k) - ub->at(k)->at(j),
                                   lb->at(k)->at(j) - ub->at(i)->at(k));
                lb->at(i)->at(j) = max(lb->at(i)->at(j), max_lb);
                ub->at(i)->at(j) = min(ub->at(i)->at(j), ub->at(i)->at(k) + ub->at(k)->at(j));
            }
        }
    }
}

int check_connected(Graph g, boost::property_map<Graph, unsigned int VertexProperties::*>::type id)
{
    int count = 0;
    unsigned int nodes = boost::num_vertices(g);
    if (nodes == 0)
    {
        return count;
    }
    list<unsigned int> queue;
    unsigned int total_visited = 0;
    vector<bool> visited(nodes, false);
    while (total_visited != nodes)
    {
        ++count;
        queue.clear();
        for (unsigned int i = 0; i < nodes; ++i)
        {
            if (!visited.at(i))
            {
                ++total_visited;
                visited.at(i) = true;
                queue.push_back(i);
                break;
            }
        }
        while (!queue.empty())
        {
            unsigned int node = queue.back();
            queue.pop_back();
            boost::graph_traits<Graph>::out_edge_iterator ei, edge_end;
            boost::graph_traits<Graph>::vertex_iterator i, end;
            for (tie(i, end) = vertices(g); i != end; ++i)
            {
                if (id[*i] == node)
                {
                    break;
                }
            }
            for (tie(ei, edge_end) = out_edges(*i, g); ei != edge_end; ++ei)
            {
                unsigned int neighbour = id[target(*ei, g)];
                if (!visited.at(neighbour))
                {
                    visited.at(neighbour) = true;
                    queue.push_back(neighbour);
                    ++total_visited;
                }
            }
        }
    }
    return count;
}

vector<list<pair<unsigned int, double>> *> *get_adjacency_list(Graph g,
                                                              boost::property_map<Graph, unsigned int VertexProperties::*>::type id,
                                                              vector<vector<double> *> *dist)
{

    vector<list<pair<unsigned int, double>> *> *adj_list = new vector<list<pair<unsigned int, double>> *>();
    boost::graph_traits<Graph>::vertex_iterator i, end;
    boost::graph_traits<Graph>::out_edge_iterator ei, edge_end;

    for (tie(i, end) = vertices(g); i != end; ++i)
    {
        unsigned int end_point1 = id[*i];
        adj_list->push_back(new list<pair<unsigned int, double>>());
        for (tie(ei, edge_end) = out_edges(*i, g); ei != edge_end; ++ei)
        {
            unsigned int end_point2 = id[target(*ei, g)];
            double distance = dist->at(end_point1)->at(end_point2);
            std::pair<unsigned int, double> pr = make_pair(end_point2, distance);
            adj_list->at(end_point1)->push_back(pr);
        }
    }
    return adj_list;
}

vector<vector<double> *> *get_adjacency_matrix(Graph g,
                                              boost::property_map<Graph, unsigned int VertexProperties::*>::type id,
                                              vector<vector<double> *> *dist, double default_missing = -1.)
{

    vector<vector<double> *> *adj_matrix = new vector<vector<double> *>();
    boost::graph_traits<Graph>::vertex_iterator i, end;
    boost::graph_traits<Graph>::out_edge_iterator ei, edge_end;
    unsigned int nodes = num_vertices(g);
    for (unsigned int i = 0; i < nodes; ++i)
    {
        adj_matrix->push_back(new vector<double>());
        for (unsigned int j = 0; j < nodes; ++j)
        {
            adj_matrix->at(i)->push_back(default_missing);
        }
        adj_matrix->at(i)->at(i) = 0.;
    }
    for (tie(i, end) = vertices(g); i != end; ++i)
    {
        unsigned int end_point1 = id[*i];
        for (tie(ei, edge_end) = out_edges(*i, g); ei != edge_end; ++ei)
        {
            unsigned int end_point2 = id[target(*ei, g)];
            double distance = dist->at(end_point1)->at(end_point2);
            adj_matrix->at(end_point1)->at(end_point2) = distance;
        }
    }
    return adj_matrix;
}

vector<vector<double> *> *distance_matrix(unsigned int nodes, unsigned int dims, unsigned p = 2)
{
    uniform_real_distribution<double> runif(-1., 1.);
    uniform_real_distribution<double> aunif(0., 2. * boost::math::constants::pi<double>());
    default_random_engine re;
    vector<vector<double> *> *dist = new vector<vector<double> *>();   // nodes X nodes
    vector<vector<double> *> *points = new vector<vector<double> *>(); // nodes X d
    double max_val = 0;
    for (unsigned int i = 0; i < nodes; ++i)
    {
        double r = runif(re);
        double entity = r;
        double angle = aunif(re);
        points->push_back(new vector<double>());
        for (unsigned int j = 1; j < dims; ++j)
        {
            points->at(i)->push_back(entity * cos(angle));
            entity *= sin(angle);
            angle = aunif(re);
        }
        points->at(i)->push_back(entity);
    }

    cout << "Allocated points" << endl;

    for (unsigned int i = 0; i < nodes; ++i)
    {
        dist->push_back(new vector<double>());
        for (unsigned int j = 0; j < nodes; ++j)
        {
            if (i == j)
            {
                dist->at(i)->push_back((double)0.);
            }
            else
            {
                double total = 0;
                for (unsigned int k = 0; k < dims; ++k)
                {
                    double val = points->at(i)->at(k) - points->at(j)->at(k);
                    if (val < 0)
                        val *= -1.;
                    total += pow(val, (double)p);
                }
                total = pow(total, (double)1. / p) / 2;
                max_val = max(max_val, total);
                dist->at(i)->push_back(total);
            }
        }
    }

    for (unsigned int i = 0; i < nodes; ++i)
    {
        if (DEBUG)
        {
            for (unsigned int j = 0; j < dims; ++j)
            {
                cout << " " << points->at(i)->at(j);
            }
            cout << endl;
        }
        delete points->at(i);
    }
    delete points;
    cout << "Maximum value encountered is " << max_val << endl;
    return dist;
}

void clean_up_adj_matrix(vector<vector<double> *> *adj_matrix)
{
    unsigned int adj_matrix_size = adj_matrix->size();
    while (adj_matrix_size-- > 0)
    {
        delete adj_matrix->at(adj_matrix_size);
    }
    delete adj_matrix;
}

void clean_up_adj_list(vector<list<pair<unsigned int, double>> *> *adj_lst)
{
    unsigned int adj_lst_size = adj_lst->size();
    while (adj_lst_size-- > 0)
    {
        delete adj_lst->at(adj_lst_size);
    }
    delete adj_lst;
}

map<pair<unsigned int, unsigned int>, double> *convert_adjList_to_knownEdges(vector<list<pair<unsigned int, double>> *> *adj_lst)
{
    map<pair<unsigned int, unsigned int>, double> *known_edges = new map<pair<unsigned int, unsigned int>, double>();
    ofstream myfile;
    std::string file_name = "graph_" + to_string(adj_lst->size()) + ".txt";
    myfile.open(file_name);
    unsigned int ctr = 0;
    for (unsigned int u = 0; u < adj_lst->size(); ++u)
    {
        list<pair<unsigned int, double>> *lst = adj_lst->at(u);
        for (auto it = lst->begin(); it != lst->end(); ++it)
        {
            pair<unsigned int, double> p = *it;
            unsigned int v = p.first, u1 = u;
            if (v < u1)
            {
                v = u1;
                u1 = p.first;
            }
            std::stringstream u_;
            std::stringstream v_;
            std::stringstream p_;
            u_ << u1;
            v_ << v;
            p_ << p.second;
            std::string out_u = u_.str();
            std::string out_v = v_.str();
            std::string out_p = p_.str();
            std::string outline = out_u + " " + out_v + " " + out_p + "\n";
            myfile << outline;
            known_edges->insert(make_pair(make_pair(u1, v), p.second));
            //            cout << "U_1 " << u1 << " " << "V " << v << endl;
            //            cout << "known edge size: " << known_edges->size() << endl;
            ++ctr;
        }
    }
    //    cout << "counter: " << ctr << endl;
    myfile.close();
    cout << "Input (Graph)File is written; You can start Python code" << endl;

    return known_edges;
}

vector<list<pair<unsigned int, double>> *> *get_adj_list_file(char *filename)
{
    vector<list<pair<unsigned int, double>> *> *adj_list = new vector<list<pair<unsigned int, double>> *>();
    ifstream ifs;
    ifs.open(filename, ifstream::in);
    unsigned int nodes;
    ifs >> nodes;
    for (int i = 0; i < nodes; i++)
    {
        adj_list->push_back(new list<pair<unsigned int, double>>());
    }
    unsigned int u, v, edge_numbers = 0;
    double dist;
    while (ifs >> u >> v >> dist)
    {
        adj_list->at(u)->push_back(make_pair(v, dist));
        adj_list->at(v)->push_back(make_pair(u, dist));
        ++edge_numbers;
        unsigned int u1 = min(u, v);
        unsigned int v1 = max(u, v);
        cout << u1 << " " << v1 << endl;
    }
    cout << "From read file" << edge_numbers << endl;
    return adj_list;
}

vector<vector<double> *> *get_adj_matrix_file(char *filename, double default_val = -1.)
{
    vector<vector<double> *> *adj_mat = new vector<vector<double> *>();
    ifstream ifs;
    ifs.open(filename, ifstream::in);
    unsigned int nodes;
    ifs >> nodes;
    for (int i = 0; i < nodes; i++)
    {
        adj_mat->push_back(new vector<double>());
        for (int j = 0; j < nodes; j++)
        {
            adj_mat->at(i)->push_back(default_val);
        }
        adj_mat->at(i)->at(i) = 0.;
    }
    unsigned int u, v;
    double dist;
    while (ifs >> u >> v >> dist)
    {
        //        cout << u << " " << v << " " << dist << endl;
        adj_mat->at(u)->at(v) = adj_mat->at(v)->at(u) = dist;
    }
    return adj_mat;
}

int main(int argc, char **argv)
{
    unsigned int init = time(NULL);
    unsigned int nodes = 1000, k = 10, sampling_size = 2000;
    double prob = 0.05;
    bool exact = false;
    cout << "This program can be run with following options" << endl;
    cout << "./edge_landmarks <random seed> <number of nodes> <edge density> <size of landmarks> <number of samples>" << endl;
    cout << "random seed - positive integer" << endl;
    cout << "number of nodes - positive integer" << endl;
    cout << "edge density - floating point number. Indicates the density of the graph." << endl;
    cout << "size of landmarks - positive integer" << endl;
    cout << "number of samples - positive integer" << endl;
    cout << "exact - should exact be run ?" << endl;
    if (argc > 1)
    {
        init = stoi(argv[1]);
    }
    if (argc > 2)
    {
        nodes = stoi(argv[2]);
    }
    if (argc > 3)
    {
        prob = stof(argv[3]);
    }
    if (argc > 4)
    {
        k = stoi(argv[4]);
    }
    if (argc > 5)
    {
        sampling_size = stoi(argv[5]);
    }
    if(argc > 6) {
        exact = stoi(argv[6]) != 0;
    }

    // Create graph with 100 nodes and edges with probability 0.05
    srand(init);
    boost::minstd_rand gen;
    Graph g(ERGen(gen, nodes, prob), ERGen(), nodes);

    boost::property_map<Graph, unsigned int VertexProperties::*>::type id = get(&VertexProperties::index, g);
    boost::graph_traits<Graph>::vertex_iterator vi, viend;

    int vert_num = 0;
    for (tie(vi, viend) = vertices(g); vi != viend; ++vi)
    {
        id[*vi] = vert_num++;
    }

    boost::graph_traits<Graph>::vertex_iterator i, end;
    boost::graph_traits<Graph>::out_edge_iterator ei, edge_end;

    int total = 0;
    for (tie(i, end) = vertices(g); i != end; ++i)
    {
        if (DEBUG)
        {
            cout << id[*i] << " ";
        }
        int count = 0;
        for (tie(ei, edge_end) = out_edges(*i, g); ei != edge_end; ++ei)
        {
            if (DEBUG)
            {
                cout << id[target(*ei, g)] << "  ";
            }
            ++count;
        }
        total += count;
        if (DEBUG)
        {
            cout << count << endl;
        }
    }
    cout << "Total nodes : " << nodes << endl;
    cout << "Total edges : " << total / 2. << endl;
    cout << "Components " << check_connected(g, id) << endl;
    cout << "Adjacency matrix" << endl;
    vector<vector<double> *> *distance = distance_matrix(nodes, 6);
    vector<list<pair<unsigned int, double>> *> *adj_lst = get_adjacency_list(g, id, distance);
    vector<vector<double> *> *adj_mat = get_adjacency_matrix(g, id, distance, (double)-1.);
    vector<vector<double> *> *lb = get_adjacency_matrix(g, id, distance, (double)0.);
    vector<vector<double> *> *ub = get_adjacency_matrix(g, id, distance, (double)1.);
    vector<vector<double> *> *lb_elm = get_adjacency_matrix(g, id, distance, (double)0.);
    map<pair<unsigned int, unsigned int>, double> *known_edges = convert_adjList_to_knownEdges(adj_lst);

    auto start_lb_elm = chrono::high_resolution_clock::now();
    // EdgeLandMark *elm = new EdgeLandMark(adj_lst, adj_mat, known_edges, nodes, k, sampling_size);
    // cout << "Sampling unknown edges" << endl;
    // elm->sample_unknown_edges();
    // cout << "Finding paths" << endl;
    // elm->find_paths();
    // cout << "Greedy sampling" << endl;
    // elm->greedy_sampling();


    
    

    //vector<list<pair<unsigned int, double>> *> *adj_list, map<pair<unsigned int, unsigned int>, double> *known_edges, unsigned int n_nodes, unsigned int k, unsigned int sampling_size)
    EdgeLandMark *elm_sampling = new EdgeLandMark(adj_lst, nodes, k, sampling_size);
    
    auto start_sampling = std::chrono::high_resolution_clock::now();
    elm_sampling->get_landmarks();
    auto stop_sampling = std::chrono::high_resolution_clock::now();
    auto duration_sampling = std::chrono::duration_cast<std::chrono::microseconds>(stop_sampling - start_sampling);

    EdgeLandMark *elm_exact = new EdgeLandMark(adj_lst, nodes, k, sampling_size);

    auto start_exact = std::chrono::high_resolution_clock::now();
    if(exact) {
        elm_exact->get_exact_landmarks();
    }
    auto stop_exact = std::chrono::high_resolution_clock::now();
    auto duration_exact = std::chrono::duration_cast<std::chrono::microseconds>(stop_exact - start_exact);


    EdgeLandMark *elm_heuristic1 = new EdgeLandMark(adj_lst, nodes, k, sampling_size);

    auto start_heuristic1 = std::chrono::high_resolution_clock::now();
    elm_heuristic1->large_edge_heuristic();
    auto stop_heuristic1 = std::chrono::high_resolution_clock::now();
    auto duration_heuristic1 = std::chrono::duration_cast<std::chrono::microseconds>(stop_heuristic1 - start_heuristic1);

    EdgeLandMark *elm_heuristic2 = new EdgeLandMark(adj_lst, nodes, k, sampling_size);

    auto start_heuristic2 = std::chrono::high_resolution_clock::now();
    elm_heuristic2->far_away_heuristic();
    auto stop_heuristic2 = std::chrono::high_resolution_clock::now();
    auto duration_heuristic2 = std::chrono::duration_cast<std::chrono::microseconds>(stop_heuristic2 - start_heuristic2);

    auto start_tri = std::chrono::high_resolution_clock::now();
    TriSearch tri = TriSearch(adj_lst, nodes);
    auto stop_tri = std::chrono::high_resolution_clock::now();
    auto duration_tri = std::chrono::duration_cast<std::chrono::microseconds>(stop_tri - start_tri);


    // double total_lb_elm = 0.;
    // for (unsigned int i = 0; i < nodes; ++i)
    // {
    //     for (unsigned int j = i + 1; j < nodes; ++j)
    //     {
    //         if (adj_mat->at(i)->at(j) < -0.1)
    //         {
    //             lb_elm->at(i)->at(j) = elm->lookup(i, j);
    //             total_lb_elm += lb_elm->at(i)->at(j);
    //         }
    //     }
    // }
    // auto stop_lb_elm = chrono::high_resolution_clock::now();
    // auto duration_lb_elm = chrono::duration_cast<chrono::microseconds>(stop_lb_elm - start_lb_elm);
    // std::cout << "Duration ELM LB:" << duration_lb_elm.count() / 1000000.0 << endl;
    // cout << "Total ELM LB : " << total_lb_elm << endl;

    double total_lb_sw = 0.;
    double graph_weight_orig = 0.;
    auto start_lb_sw = chrono::high_resolution_clock::now();
    // SashaWang(lb, ub);
    compute_lb(adj_lst, adj_mat, lb);
    auto stop_lb_sw = chrono::high_resolution_clock::now();
    auto duration_lb_sw = chrono::duration_cast<chrono::microseconds>(stop_lb_sw - start_lb_sw);

    double relative = 0.;
    unsigned int relative_count = 0;
    double rmse_tri = 0.0, relative_tri = 0.0;
    vector<double> rmse_exact, rmse_h1, rmse_h2, rmse_sampling;
    vector<double> relative_exact, relative_h1, relative_h2, relative_sampling;
    for(unsigned int i=0; i<k; ++i) {
        rmse_exact.push_back(0.0);
        rmse_h1.push_back(0.0);
        rmse_h2.push_back(0.0);
        rmse_sampling.push_back(0.0);
        relative_exact.push_back(0.0);
        relative_h1.push_back(0.0);
        relative_h2.push_back(0.0);
        relative_sampling.push_back(0.0);
    }

    auto dummy = chrono::high_resolution_clock::now();
    chrono::microseconds duration_tri_runtime=  chrono::duration_cast<chrono::microseconds>(dummy-dummy), duration_sampling_runtime=chrono::duration_cast<chrono::microseconds>(dummy-dummy);
    for (unsigned int i = 0; i < nodes; ++i)
    {
        for (unsigned int j = i + 1; j < nodes; ++j)
        {
            if (adj_mat->at(i)->at(j) < -0.1)
            {
                if (lb->at(i)->at(j) > 0)
                {
                    vector<double>* temp_exact;
                    if(exact) {
                        temp_exact = elm_exact->lookup_multiple(i, j);
                    }
                    vector<double>* temp_sampling = elm_sampling->lookup_multiple(i, j);
                    vector<double>* temp_h1 = elm_heuristic1->lookup_multiple(i, j);
                    vector<double>* temp_h2 = elm_heuristic2->lookup_multiple(i, j);
                    for(unsigned index_i =0; index_i < k; ++index_i) {
                        if(exact) {
                            rmse_exact.at(index_i) += ((temp_exact->at(index_i) - lb->at(i)->at(j)) * (temp_exact->at(index_i) - lb->at(i)->at(j)));
                            relative_exact.at(index_i) += 1 - (temp_exact->at(index_i)/lb->at(i)->at(j));
                        }
                        
                        rmse_sampling.at(index_i) += (temp_sampling->at(index_i) - lb->at(i)->at(j)) * (temp_sampling->at(index_i) - lb->at(i)->at(j));
                        relative_sampling.at(index_i) += 1 - (temp_sampling->at(index_i)/lb->at(i)->at(j));
                        
                        rmse_h1.at(index_i) += ((temp_h1->at(index_i) - lb->at(i)->at(j)) * (temp_h1->at(index_i) - lb->at(i)->at(j)));
                        relative_h1.at(index_i) += 1 - (temp_h1->at(index_i)/lb->at(i)->at(j));
                        
                        rmse_h2.at(index_i) += ((temp_h2->at(index_i) - lb->at(i)->at(j)) * (temp_h2->at(index_i) - lb->at(i)->at(j)));
                        relative_h2.at(index_i) += 1 - (temp_h2->at(index_i)/lb->at(i)->at(j));
                    }
                    if(exact) {
                        delete temp_exact;
                    }
                    delete temp_h1;
                    delete temp_h2;
                    delete temp_sampling;


                    auto start_timer = chrono::high_resolution_clock::now();
                    tri.lookup(i, j);
                    auto end_timer = chrono::high_resolution_clock::now();
                    duration_tri_runtime += chrono::duration_cast<chrono::microseconds>(end_timer - start_timer);

                    start_timer = chrono::high_resolution_clock::now();
                    elm_sampling->lookup(i, j);
                    end_timer = chrono::high_resolution_clock::now();
                    duration_sampling_runtime += chrono::duration_cast<chrono::microseconds>(end_timer - start_timer);

                    rmse_tri += ((tri.lookup(i, j) - lb->at(i)->at(j)) * (tri.lookup(i, j) - lb->at(i)->at(j)));
                    relative_tri += (1 - (tri.lookup(i, j) / lb->at(i)->at(j)));
                    relative_count++;
                    total_lb_sw += lb->at(i)->at(j);

                }
            }
            else
            {
                graph_weight_orig += lb->at(i)->at(j);
            }
        }
    }

    std::cout << "Runtime Sampling:" << duration_sampling_runtime.count() / 1000000.0 << endl;
    std::cout << "Runtime TriSearch:" << duration_tri_runtime.count() / 1000000.0 << endl;
    std::cout << "Duration SW LB:" << duration_lb_sw.count() / 1000000.0 << endl;
    if(exact) {
        std::cout << "Duration Exact:" << duration_exact.count() / 1000000.0 << endl;
    }
    std::cout << "Duration Sampling:" << duration_sampling.count() / 1000000.0 << endl;
    std::cout << "Duration Heuristic1:" << duration_heuristic1.count() / 1000000.0 << endl;
    std::cout << "Duration Heuristic2:" << duration_heuristic2.count() / 1000000.0 << endl;
    std::cout << "Duration TriSearch:" << duration_tri.count() / 1000000.0 << endl;
    // cout << "Total Original Graph weight : " << graph_weight_orig << endl;
    // cout << "Total SW LB : " << total_lb_sw << endl;
    for(unsigned index_i =0; index_i < k; ++index_i) {
        cout << "root mean square error sampling for sampling " << index_i << ": " << sqrt(rmse_sampling.at(index_i) / relative_count) << endl;
        cout << "Sum Relative Error on edge for sampling : " << index_i << ": " << (relative_sampling.at(index_i) / relative_count) << endl;

        if(exact) {
            cout << "root mean square error exact " << index_i << ": " << sqrt(rmse_exact.at(index_i) / relative_count) << endl;
            cout << "Sum Relative Error on edge for exact : " << index_i << ": " << (relative_exact.at(index_i) / relative_count) << endl;
        }
        
        cout << "root mean square error H1 " << index_i << ": " << sqrt(rmse_h1.at(index_i) / relative_count) << endl;
        cout << "Sum Relative Error on edge for H1 : " << index_i << ": " << (relative_h1.at(index_i) / relative_count) << endl;

        cout << "root mean square error H2 " << index_i << ": " << sqrt(rmse_h2.at(index_i) / relative_count) << endl;
        cout << "Sum Relative Error on edge for H2 : " << index_i << ": " << (relative_h2.at(index_i) / relative_count) << endl;
    }
    cout << "root mean square error tri: " << sqrt(rmse_tri / relative_count) << endl;
    cout << "Sum Relative Error on edge tri: " << (relative_tri / relative_count) << endl;

    delete elm_exact;
    delete elm_heuristic1;
    delete elm_heuristic2;
    delete elm_sampling;
    delete known_edges;
    clean_up_adj_list(adj_lst);
    clean_up_adj_matrix(adj_mat);
    clean_up_adj_matrix(lb);
    clean_up_adj_matrix(ub);
    clean_up_adj_matrix(lb_elm);
    // cout << "Distances " << endl;
    for (unsigned int i = 0; i < nodes; ++i)
    {
        if (DEBUG)
        {
            for (unsigned int j = 0; j < nodes; ++j)
            {
                cout << " " << distance->at(i)->at(j);
            }
            cout << endl;
        }
        delete distance->at(i);
    }
    delete distance;
    return 0;
}