#include <map>
#include <list>
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream> 
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/erdos_renyi_generator.hpp>
#include <boost/random/linear_congruential.hpp>
#include <utility>
#include <random>
#include <cmath>
#include <boost/math/constants/constants.hpp>

using namespace std;

unsigned int p_norm = 2;

struct VertexProperties
{
    unsigned int index;
};

typedef boost::adjacency_list<boost::vecS, boost::listS, boost::undirectedS, VertexProperties> Graph;
typedef boost::erdos_renyi_iterator<boost::minstd_rand, Graph> ERGen;

vector<list<pair<unsigned int, double>> *> *get_adjacency_list(Graph g,
                                                              boost::property_map<Graph, unsigned int VertexProperties::*>::type id,
                                                              vector<vector<double> *> *points)
{

    vector<list<pair<unsigned int, double>> *> *adj_list = new vector<list<pair<unsigned int, double>> *>();
    boost::graph_traits<Graph>::vertex_iterator i, end;
    boost::graph_traits<Graph>::out_edge_iterator ei, edge_end;

    unsigned int dims = points->at(0)->size();

    for (tie(i, end) = vertices(g); i != end; ++i)
    {
        unsigned int end_point1 = id[*i];
        adj_list->push_back(new list<pair<unsigned int, double>>());
        for (tie(ei, edge_end) = out_edges(*i, g); ei != edge_end; ++ei)
        {
            unsigned int end_point2 = id[target(*ei, g)];

            double distance = 0;
            for (unsigned int k = 0; k < dims; ++k)
            {
                double val = points->at(end_point1)->at(k) - points->at(end_point2)->at(k);
                if (val < 0)
                    val *= -1.;
                distance += pow(val, (double)p_norm);
            }
            distance = pow(distance, (double)1. / p_norm) / dims;

            std::pair<unsigned int, double> pr = make_pair(end_point2, distance);
            adj_list->at(end_point1)->push_back(pr);
        }
    }
    return adj_list;
}


void write_adj_list_to_file(vector<list<pair<unsigned int, double>> *> *adj_lst, char* filename)
{
    ofstream myfile;
    // std::string file_name = "graph_" + to_string(adj_lst->size()) + ".txt";
    myfile.open(filename);
    myfile << adj_lst->size() << endl;
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
            //            cout << "U_1 " << u1 << " " << "V " << v << endl;
            //            cout << "known edge size: " << known_edges->size() << endl;
            ++ctr;
        }
    }
    //    cout << "counter: " << ctr << endl;
    myfile.close();
    cout << "Input (Graph)File is written; You can start Python code" << endl;
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

vector<vector<double> *> * get_points(unsigned int nodes, unsigned int dims)
{
    uniform_real_distribution<double> runif(-1., 1.);
    uniform_real_distribution<double> aunif(0., 2. * boost::math::constants::pi<double>());
    default_random_engine re;
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

    return points;
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

int main(int argc, char **argv) {
    unsigned int init = time(NULL);
    unsigned int nodes = 1000, dims;
    double prob = 0.05;
    cout << "This program can be run with following options" << endl;
    cout << "./edge_landmarks <number of nodes> <edge density> <dims> <filename>" << endl;
    cout << "number of nodes - positive integer" << endl;
    cout << "edge density - floating point number. Indicates the density of the graph." << endl;
    cout << "dims - number of dimensions used in generation of dataset" << endl;
    cout << "filename - name of file" << endl;

    if (argc < 4)
    {
        cout << "Improper arguments!" << endl;
        return -1;
    }

    nodes = stoi(argv[1]);
    prob = stof(argv[2]);
    dims = stoi(argv[3]);
    char *filename = argv[4];

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
        // cout << id[*i] << " ";
        int count = 0;
        for (tie(ei, edge_end) = out_edges(*i, g); ei != edge_end; ++ei)
        {
            ++count;
        }
        total += count;
    }
    cout << "Total nodes : " << nodes << endl;
    cout << "Total edges : " << total / 2 << endl;
    cout << "Components " << check_connected(g, id) << endl;
    cout << "Adjacency matrix" << endl;
    vector<vector<double>*>* points = get_points(nodes, dims);
    vector<list<pair<unsigned int, double>> *> *adj_lst = get_adjacency_list(g, id, points);
    write_adj_list_to_file(adj_lst, filename);
    clean_up_adj_matrix(points);
    clean_up_adj_list(adj_lst);

    return 0;
}