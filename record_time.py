import subprocess
import copy
import csv
import json

args = ['./a.out']
with open('time_Erdos.csv', 'w', newline='') as csvfile:
    fieldnames = ['Seed', 'Nodes', 'Prob', 'SW', 'LB', 'UB']
    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
    writer.writeheader()
    for seed in range(30):
        for nodes in range(1000, 10000, 1000):
            for p in range(10, 99, 10):
                prob = p / 100.
                arguments = copy.copy(args)
                arguments.append(str(seed))
                arguments.append(str(nodes))
                arguments.append(str(prob))
                out = subprocess.Popen(arguments, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                stdout,stderr = out.communicate()
                stdout = stdout.decode()
                stdout_line = stdout.split('\n')
                duration = list(filter(lambda x: x.find('Duration') != -1, stdout.split('\n')))
                times = list(map(lambda x: float(x.split(':')[1]), duration))
                obj = {'Seed': str(seed), 'Nodes': str(nodes), 'Prob': str(prob),  'SW': str(times[0]), 'LB': str(times[1]), 'UB': '-1'}
                print(json.dumps(obj, indent=4))
                writer.writerow(obj)
