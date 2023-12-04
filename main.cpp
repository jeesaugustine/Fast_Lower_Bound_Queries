#include <iostream>
#include <boost/heap/pairing_heap.hpp>
#include <ctime>
#include <cstdlib>
#include <vector>
#include <boost/math/constants/constants.hpp>
#include <string>
#include <chrono>

/*

TODO:
====
1. Serialize output
*/

#include <boost/config.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/erdos_renyi_generator.hpp>
#include <boost/random/linear_congruential.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/property_map/property_map.hpp>
#include <boost/graph/connected_components.hpp>
#include <utility>
#include <list>
#include <map>
#include <random>
#include <cmath>

using namespace boost::heap;
using namespace boost;
using namespace std;

const int DEBUG = 0;

class path {
private:
    pair <size_t, size_t> edge;
    double distance;
public:
    path(size_t end_point1, size_t end_point2, double dist) {
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

    pair<size_t, size_t> get_edge() const {
        return edge;
    }

    void set_distance(double dist) {
        distance = dist;
    }

    bool operator <(const path & pathObj) const    {
        return distance < pathObj.distance;
    }
};

struct VertexProperties {
  size_t index;
};

typedef adjacency_list<vecS, listS, undirectedS, VertexProperties> Graph;
typedef erdos_renyi_iterator<boost::minstd_rand, Graph> ERGen;

int check_connected(Graph g, property_map<Graph, size_t VertexProperties::*>::type id) {
    int count = 0;
    size_t nodes = num_vertices(g);
    if(nodes == 0) {
        return count;
    }
    list<size_t> queue;
    size_t total_visited = 0;
    vector<bool> visited(nodes, false);
    while(total_visited != nodes) {
        ++count;
        queue.clear();
        for(size_t i=0; i < nodes;++i) {
            if(!visited.at(i)) {
                ++total_visited;
                visited.at(i) = true;
                queue.push_back(i);
                break;
            }
        }
        while(!queue.empty()) {
            size_t node = queue.back();
            queue.pop_back();
            graph_traits<Graph>::out_edge_iterator ei, edge_end;
            graph_traits<Graph>::vertex_iterator i, end;
            for (tie(i,end) = vertices(g); i != end; ++i) {
                if(id[*i] == node) {
                    break;
                }
            }
            for (tie(ei,edge_end) = out_edges(*i, g); ei != edge_end; ++ei) {
                size_t neighbour = id[target(*ei, g)];
                if(!visited.at(neighbour)) {
                    visited.at(neighbour) = true;
                    queue.push_back(neighbour);
                    ++total_visited;
                }
            }
        }
    }
    return count;
}

void compute_ub(vector<list<pair<size_t, double>>*>* adj_lst,
        vector<vector<double>*>* adj_mat, vector<vector<double>*>* ub_mat) {
    size_t nodes = adj_lst->size();
    vector<bool> visited;
    for(size_t i = 0; i < nodes; ++i) {
        visited.push_back(false);
    }
    for(size_t start_node = 0; start_node < nodes; ++start_node) {
        for(size_t start_node = 0; start_node < nodes; ++start_node) {
            visited.at(start_node) = false;
        }
        // Run Dijkstra from current node
        pairing_heap<path> H;
        map<size_t, pairing_heap<path>::handle_type> handles;

        H.push(path(start_node, start_node, 0.));
        while(!H.empty()) {
            auto edge = H.top().get_edge();
            double path_len = -H.top().get_distance();
            if(path_len >= 1.0) {
                // Break out of while loop
                break;
            }
            size_t path_end_point = (edge.first == start_node) ? edge.second : edge.first;
            visited.at(path_end_point) = true; // Fix the path to path_end_point and its length
            // Update the upper bound matrix
            ub_mat->at(start_node)->at(path_end_point) = min(1.0, path_len);
            ub_mat->at(path_end_point)->at(start_node) = min(1.0, path_len);
            H.pop();
            auto map_it = handles.find(path_end_point);
            if(map_it != handles.end()) {
                handles.erase(map_it);
            }
            for(auto it = adj_lst->at(path_end_point)->begin(); it != adj_lst->at(path_end_point)->end(); ++it) {
                size_t end_point = it->first; // Expand along (path_end_point, end_point)
                if(visited.at(end_point)) {
                    continue;
                }
                double edge_len = it->second;
                if(edge_len + path_len >= 1.0) {
                    // Too large already
                    continue;
                }
                auto map_it = handles.find(end_point);
                if(map_it != handles.end()) {
                    // Check if edge length is smaller
                    if(-(map_it->second.node_->value.get_distance()) > (edge_len + path_len)) {
                        pairing_heap<path>::handle_type map_handle = map_it->second;
                        H.increase(map_handle, path(start_node, end_point, -(edge_len + path_len)));
                    }
                } else {
                    // Insert into heap and handle into map
                    pairing_heap<path>::handle_type hand_endpnt = H.push(path(start_node, end_point, -(edge_len + path_len)));
                    pair<size_t, pairing_heap<path>::handle_type> map_pair = make_pair(end_point, hand_endpnt);
                    handles.insert(map_pair);
                }
            }
        }
        //H.clear();
    }
}

void compute_lb(vector<list<pair<size_t, double>>*>* adj_lst,
        vector<vector<double>*>* adj_mat, vector<vector<double>*>* lb_mat) {
    pairing_heap<path> H;
    size_t nodes = adj_lst->size();
    vector<bool> unknown(nodes, true);
    vector<vector<pairing_heap<path>::handle_type>> handles;
    for(size_t i = 0; i < nodes; ++i) {
        vector<pairing_heap<path>::handle_type> v;
        for(size_t j = 0; j < nodes; ++j) {
            unknown.at(j) = true;
            v.push_back((pairing_heap<path>::handle_type)NULL);
        }
        unknown.at(i) = false;
        for (list<pair<size_t, double>>::iterator it=adj_lst->at(i)->begin();
                it != adj_lst->at(i)->end(); ++it) {
            size_t end = it->first;
            unknown.at(end) = false;
        }
        for(size_t j = 0; j < i; ++j) {
            v.at(j) = handles.at(j).at(i);
        }
        for(size_t j = i + 1; j < nodes; ++j) {
            if(unknown.at(j)) {
                v.at(j) = H.push(path(i, j, 0.));
            }
        }
        handles.push_back(v);
    }
    // All paths of length 2
    for(size_t i = 0; i < nodes; ++i) {
        auto end = adj_lst->at(i)->end();
        for (auto it=adj_lst->at(i)->begin();it != end; ++it) {
            for(auto it_fwd = std::next(it); it_fwd != end; ++it_fwd) {
                size_t end1 = it->first, end2 = it_fwd->first;
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
            size_t end_point = it->first;
            size_t min_end = min(end_point, edge.second), max_end = max(end_point, edge.second);
            if(adj_mat->at(min_end)->at(max_end) < 0.) {
                double val = dist - it->second;
                if(val > handles.at(min_end).at(max_end).node_->value.get_distance()) {
                    H.increase(handles.at(min_end).at(max_end), path(min_end, max_end, val));
                }
            }
        }
        for (auto it=adj_lst->at(edge.second)->begin();it != adj_lst->at(edge.second)->end(); ++it) {
            // Update lengths of edges on heap
            size_t end_point = it->first;
            size_t min_end = min(end_point, edge.first), max_end = max(end_point, edge.first);
            if(adj_mat->at(min_end)->at(max_end) < 0.) {
                double val = dist - it->second;
                if(val > handles.at(min_end).at(max_end).node_->value.get_distance()) {
                    H.increase(handles.at(min_end).at(max_end), path(min_end, max_end, val));
                }
            }
        }
    }
}

void clean_up_adj_list(vector<list<pair<size_t, double>>*>* adj_lst) {
    size_t adj_lst_size = adj_lst->size();
    while(adj_lst_size-- > 0) {
        delete adj_lst->at(adj_lst_size);
    }
    delete adj_lst;
}


vector<list<pair<size_t, double>>*>* get_adjacency_list(Graph g,
        property_map<Graph, size_t VertexProperties::*>::type id,
        vector<vector<double>*>* dist) {

    vector<list<pair<size_t, double>>*>* adj_list = new vector<list<pair<size_t, double>>*>();
    graph_traits<Graph>::vertex_iterator i, end;
    graph_traits<Graph>::out_edge_iterator ei, edge_end;

    for (tie(i,end) = vertices(g); i != end; ++i) {
        size_t end_point1 = id[*i];
        adj_list->push_back(new list<pair<size_t, double>>());
        for (tie(ei,edge_end) = out_edges(*i, g); ei != edge_end; ++ei) {
            size_t end_point2 = id[target(*ei, g)];
            double distance = dist->at(end_point1)->at(end_point2);
            std::pair<size_t, double> pr = make_pair(end_point2, distance);
            adj_list->at(end_point1)->push_back(pr);
        }
    }
    return adj_list;
}

void clean_up_adj_matrix(vector<vector<double>*>* adj_matrix) {
    size_t adj_matrix_size = adj_matrix->size();
    while(adj_matrix_size-- > 0) {
        delete adj_matrix->at(adj_matrix_size);
    }
    delete adj_matrix;
}

vector<vector<double>*>* get_adjacency_matrix(Graph g,
        property_map<Graph, size_t VertexProperties::*>::type id,
        vector<vector<double>*>* dist, double default_missing = -1.) {

    vector<vector<double>*>* adj_matrix = new vector<vector<double>*>();
    graph_traits<Graph>::vertex_iterator i, end;
    graph_traits<Graph>::out_edge_iterator ei, edge_end;
    size_t nodes = num_vertices(g);
    for(size_t i =0; i < nodes; ++i) {
        adj_matrix->push_back(new vector<double>());
        for(size_t j =0; j < nodes; ++j) {
            adj_matrix->at(i)->push_back(default_missing);
        }
        adj_matrix->at(i)->at(i) = 0.;
    }
    for (tie(i,end) = vertices(g); i != end; ++i) {
        size_t end_point1 = id[*i];
        for (tie(ei,edge_end) = out_edges(*i, g); ei != edge_end; ++ei) {
            size_t end_point2 = id[target(*ei, g)];
            double distance = dist->at(end_point1)->at(end_point2);
            adj_matrix->at(end_point1)->at(end_point2) = distance;
        }
    }
    return adj_matrix;
}

void SashaWang(vector<vector<double>*>* lb, vector<vector<double>*>* ub) {
    size_t nodes = lb->size();
    for(size_t k=0; k < nodes; ++k) {
        for(size_t j=0; j < nodes; ++j) {
            for(size_t i=0; i < nodes; ++i) {
                double max_lb = max(lb->at(i)->at(k) - ub->at(k)->at(j), 
                                    lb->at(k)->at(j) - ub->at(i)->at(k));
                lb->at(i)->at(j) = max(lb->at(i)->at(j), max_lb);
                ub->at(i)->at(j) = min(ub->at(i)->at(j), ub->at(i)->at(k) + ub->at(k)->at(j));
            }
        }
    }
}

vector<vector<double>*>* distance_matrix(size_t nodes, size_t dims, unsigned p=2) {
    uniform_real_distribution<double> runif(-1.,1.);
    uniform_real_distribution<double> aunif(0.,2.*boost::math::constants::pi<double>());
    default_random_engine re;
    vector<vector<double>*>* dist = new vector<vector<double>*>(); // nodes X nodes
    vector<vector<double>*>* points = new vector<vector<double>*>(); // nodes X d
    double max_val = 0;
    for(size_t i=0;i < nodes; ++i){
        double r = runif(re);
        double entity = r;
        double angle = aunif(re);
        points->push_back(new vector<double>());
        for(size_t j = 1; j < dims; ++j) {
            points->at(i)->push_back(entity * cos(angle));
            entity *= sin(angle);
            angle = aunif(re);
        }
        points->at(i)->push_back(entity);
    }

    cout << "Allocated points" << endl;

    for(size_t i=0;i < nodes; ++i){
        dist->push_back(new vector<double>());
        for(size_t j=0;j < nodes; ++j){
            if(i==j){
                dist->at(i)->push_back(0.);
            } else {
                double total = 0;
                for(size_t k =0; k < dims; ++k) {
                    double val = points->at(i)->at(k) - points->at(j)->at(k);
                    if(val < 0)
                        val *= -1.;
                    total += pow(val, (double)p);
                }
                total = pow(total, (double)1./p)/2;
                max_val = max(max_val, total);
                dist->at(i)->push_back(total);
            }
        }
    }

    for(size_t i=0;i < nodes; ++i){
        if(DEBUG) {
            for(size_t j=0;j < dims; ++j){
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

int main(int argc, char **argv) {
    size_t init = time(NULL);
    size_t nodes = 500; //1000;
    float prob = 0.2;
    if(argc > 1) {
        init = stoi(argv[1]);
    }
    if(argc > 2) {
        nodes = stoi(argv[2]);
    }
    if(argc > 3) {
        prob = stof(argv[3]);
    }

    srand(init);
    boost::minstd_rand gen;
    Graph g(ERGen(gen, nodes, prob), ERGen(), nodes);

    property_map<Graph, size_t VertexProperties::*>::type id = get(&VertexProperties::index, g);

    graph_traits<Graph>::vertex_iterator vi, viend;
    int vnum = 0;
    for (tie(vi,viend) = vertices(g); vi != viend; ++vi) {
        id[*vi] = vnum++;
    }

    graph_traits<Graph>::vertex_iterator i, end;
    graph_traits<Graph>::out_edge_iterator ei, edge_end;

    int total = 0;
    for (tie(i,end) = vertices(g); i != end; ++i) {
        if(DEBUG) {
            cout << id[*i] << " ";
        }
        int count = 0;
        for (tie(ei,edge_end) = out_edges(*i, g); ei != edge_end; ++ei) {
            if(DEBUG) {
                cout << id[target(*ei, g)] << "  ";
            }
            ++count;
        }
        total += count;
        if(DEBUG) {
            cout << count << endl;
        }
    }
    cout << "Total nodes : " << nodes << endl;
    cout << "Total edges : " << total/2. << endl;
    cout << "Components " << check_connected(g, id) << endl;
    cout << "Adjacency matrix" << endl;
    vector<vector<double>*>* distance = distance_matrix(nodes, 6);
    vector<list<pair<size_t, double>>*>* adj_lst = get_adjacency_list(g, id, distance);
    vector<vector<double>*>* adj_mat = get_adjacency_matrix(g, id, distance, -1.);
    vector<vector<double>*>* lb = get_adjacency_matrix(g, id, distance, 0.);
    vector<vector<double>*>* ub = get_adjacency_matrix(g, id, distance, 1.);
    if(DEBUG) {
        for(size_t i=0; i< nodes; ++i){
            for(size_t j=0; j< nodes; ++j){
                cout << to_string(adj_mat->at(i)->at(j)) << " " ;
            }
            cout << endl;
        }
        for(size_t i=0; i< nodes; ++i){
            for(size_t j=0; j< nodes; ++j){
                cout << to_string(lb->at(i)->at(j)) << " " ;
            }
            cout << endl;
        }
    }
    auto start = std::chrono::high_resolution_clock::now();
    SashaWang(lb, ub);
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    std::cout << "Duration:" <<  duration.count()/1000000.0 << std::endl;
    for(size_t i =0; i<nodes; ++i) {
        for(size_t j=0; j<nodes; ++j) {
            if(distance->at(i)->at(j) - ub->at(i)->at(j) > 0.0001) {
                cout << "Violation - UB!" << endl;
            }
            if(lb->at(i)->at(j) - distance->at(i)->at(j) > 0.0001) {
                cout << "Violation - LB!" << endl;
            }
        }
    }
    if(DEBUG) {
        for(size_t i=0; i< nodes; ++i){
            for(size_t j=0; j< nodes; ++j){
                cout << to_string(lb->at(i)->at(j)) << " " ;
            }
            cout << endl;
        }
    }
    vector<vector<double>*>* lb_our = get_adjacency_matrix(g, id, distance, 0.);
    vector<vector<double>*>* ub_our = get_adjacency_matrix(g, id, distance, 1.);
    auto start1 = std::chrono::high_resolution_clock::now();
    compute_lb(adj_lst, adj_mat, lb_our);
    auto stop1 = std::chrono::high_resolution_clock::now();
    compute_ub(adj_lst, adj_mat, ub_our);
    auto stop2 = std::chrono::high_resolution_clock::now();
    auto duration1 = std::chrono::duration_cast<std::chrono::microseconds>(stop1 - start1);
    auto duration2 = std::chrono::duration_cast<std::chrono::microseconds>(stop2 - start1);
    std::cout << "Duration Our:" <<  duration1.count()/1000000.0 << std::endl;
    std::cout << "Duration Our total:" << duration2.count()/1000000.0 << std::endl;
    for(size_t i =0; i<nodes; ++i) {
        for(size_t j=0; j<nodes; ++j) {
            if(distance->at(i)->at(j) - ub_our->at(i)->at(j) > 0.0001) {
                cout << "Violation - UB!" << endl;
            }
            if(lb_our->at(i)->at(j) - distance->at(i)->at(j) > 0.0001) {
                cout << "Violation - LB_OUR!" << endl;
            }
        }
    }
    for(size_t i =0; i<nodes; ++i) {
        for(size_t j=0; j<nodes; ++j) {
            if(abs(lb_our->at(i)->at(j) - lb->at(i)->at(j)) > 0.0001) {
                cout << "Violation - Difference SW!" << endl;
            }
            if(abs(ub_our->at(i)->at(j) - ub->at(i)->at(j)) > 0.0001) {
                cout << "Violation - Difference SW!" << ub_our->at(i)->at(j) << " " << ub->at(i)->at(j) << endl;
            }
        }
    }
    clean_up_adj_list(adj_lst);
    clean_up_adj_matrix(adj_mat);
    clean_up_adj_matrix(lb);
    clean_up_adj_matrix(ub);
    clean_up_adj_matrix(lb_our);
    clean_up_adj_matrix(ub_our);
    //cout << "Distances " << endl;
    for(size_t i=0;i < nodes; ++i){
        if(DEBUG) {
            for(size_t j=0;j < nodes; ++j){
                cout << " " << distance->at(i)->at(j);
            }
            cout << endl;
        }
        delete distance->at(i);
    }
    delete distance;
    return 0;
}