#symmetric strategy iteration and an exponential running time counterexample
#by Matthew Maat

from graph import *
from graph_io import *
import math
import copy
def decompose_scc(G):
    #decompose G into strongly connected components
    decomp=[]
    reachedlists=[]
    reachablelists=[]
    remaining_vertices=set(G.vertices)
    while remaining_vertices!=set():
        r=list(remaining_vertices)
        r0=r[0]
        reachable={r0}
        reached={r0}
        stack=[r0]
        while len(stack)>0: #bfs what they can reach
            current_vertex=stack.pop(0)
            E=current_vertex.incidence
            for e in E:
                if e.tail==current_vertex:
                    if e.head not in reachable:
                        stack.append(e.head)
                        reachable.add(e.head)
        stack=[r0]
        while len(stack)>0: #bfs if they can be reached
            current_vertex=stack.pop(0)
            E=current_vertex.incidence
            for e in E:
                if e.head==current_vertex:
                    if e.tail not in reached:
                        stack.append(e.tail)
                        reached.add(e.tail)
        ints=reached.intersection(reachable)
        reachedlist=[]
        reachablelist=[]
        for d in range(len(decomp)):
            lizzt=list(decomp[d])
            el=lizzt[0]
            if el in reachable:
                reachablelist.append(d)
            elif el in reached:
                reachedlist.append(d)
        reachablelists.append(reachablelist)
        reachedlists.append(reachedlist)
        decomp.append(ints)
        remaining_vertices=remaining_vertices.difference(ints)
    for i in range(len(reachedlists)):
        for j in reachedlists[i]:
            reachablelists[j].append(i)
    return decomp, reachablelists #reachablelists[i] has components that component i can reach

def find_lambda(G, stratplayer):
    #find best cycle for a player in a strongly connected subgraph using BFS
    #G: graph, stratplayer: player doing the counterstrategy
    bestval=-1
    bestvertex = None
    for v in G.vertices:
        reachable = set()
        stack = [v]
        stop=False
        while len(stack) > 0 and not stop:  # bfs what they can reach
            current_vertex = stack.pop(0)
            E = current_vertex.incidence
            for e in E:
                if e.tail == current_vertex:
                    if e.head==v:
                        stop=True
                    elif e.head not in reachable and e.head.label<v.label:
                        stack.append(e.head)
                        reachable.add(e.head)
                if stop:
                    break
        if stop:
            if bestval==-1:
                bestval=v.label
                bestvertex=v
            elif stratplayer==True and bestval*pow(-1, bestval)>v.label*pow(-1,v.label):
                bestval=v.label
                bestvertex=v
            elif stratplayer == False and bestval * pow(-1, bestval) < v.label * pow(-1, v.label):
                bestval = v.label
                bestvertex = v
    return bestval, bestvertex

def set_lambdas(decomp, reachablelists, stratplayer):
    #set the first component of the valuation for the nodes in the graph
    #decomp: decomposition into strongly connected components
    #reachablelists: list of which components can reach which components
    #stratplayer: player other than the one currently trying to find a valuation for
    lambdalist=[]
    lambdadict={}
    for i in range(len(decomp)): #find lambdas for each connected component
        H,I=induced_subgraph(decomp[i])
        bestval, bestvertex=find_lambda(H, stratplayer)
        lambdalist.append(bestval)
    for i in range(len(decomp)): #see what the best component is that component i can reach
        bestnum=lambdalist[i]
        for j in reachablelists[i]:
            if bestnum==-1 and lambdalist[j]!=-1:
                lambdalist[i] = lambdalist[j]
                bestnum = lambdalist[j]
            elif stratplayer and lambdalist[j]!=-1 and pow(-1, lambdalist[j])*lambdalist[j] < pow(-1,bestnum)*bestnum:
                lambdalist[i]=lambdalist[j]
                bestnum=lambdalist[j]
            elif (not stratplayer) and lambdalist[j]!=-1 and pow(-1, lambdalist[j])*lambdalist[j] > pow(-1,bestnum)*bestnum:
                lambdalist[i]=lambdalist[j]
                bestnum=lambdalist[j]
    for i in range(len(decomp)):
        for v in decomp[i]:
            v.set_lambda(stratplayer, lambdalist[i]) #stratplayer is the one doing the counterstrategy
    for l in lambdalist:
        for v in HH.vertices:
            if v.label==l:
                lambdadict[l]=v
    return lambdadict

def induced_subgraph(vertexset):
    #construct induced subgraph based on vertex set
    H=Graph(True, 0, False)
    listsz=list(vertexset)
    dictz={listsz[d].index:d for d in range(len(listsz))}
    for d in range(len(listsz)):
        v=Vertex(H,listsz[d].label, listsz[d].player, d)
        H.add_vertex(v)
    for d in range(len(listsz)):
        E=listsz[d].incidence
        for e in E:
            if e.tail==listsz[d] and e.head in vertexset:
                H.add_edge(Edge(H.vertices[d], H.vertices[dictz[e.head.index]]))
    return H,listsz

def set_shortest_paths(G, lambdadict, counterplayer):
    #set shortest paths for the whole graph, per subgraph with the same value of lambda
    #G: graph
    #lambdadict: dictionary of lambdas
    #counterplayer: other player than the one currently trying to find the valuation for
    global Gsp, targetvertex
    for l in lambdadict.keys():
        if counterplayer:
            relevantvertices = {v for v in G.vertices if v.valuation0[0]==l}
        else:
            relevantvertices = {v for v in G.vertices if v.valuation1[0]==l}
        Gsp, listsz = induced_subgraph(relevantvertices)
        for v in Gsp.vertices:
            if v.label==l:
                targetvertex=v
                break
        set_shortest_path(counterplayer)
        for ll in range(len(listsz)):
            if counterplayer:
                listsz[ll].set_path(counterplayer,Gsp.vertices[ll].valuation0[1:3])
            else:
                listsz[ll].set_path(counterplayer, Gsp.vertices[ll].valuation1[1:3])
    return

def set_shortest_path(counterplayer):
    #calculate shortest or longest paths towards the node that dominates the cycle
    #if counterplayer is False(player 0), then find longest paths, else, find shortest paths
    global Gsp, targetvertex
    priorities=[]
    priodict={}
    for e in targetvertex.incidence:
        if targetvertex==e.tail:
            Gsp.remove_edge(e)
    for v in Gsp.vertices:
        if v.label>targetvertex.label:
            priorities.append(v.label)
            priodict[v.label]=v
    priorities.sort()
    priorities=priorities[::-1] #sorted from high to low
    for p in priorities: #priority of r
        if (p%2==0 and counterplayer==True) or (p%2==1 and counterplayer==False):
            W = {targetvertex} #vertices with path to t without r
            stack = [targetvertex]
            while len(stack) > 0:  # bfs what can reach t
                current_vertex = stack.pop(0)
                E = current_vertex.incidence
                for e in E:
                    if e.head== current_vertex:
                        if e.tail not in W and e.tail!=priodict[p]:
                            stack.append(e.tail)
                            W.add(e.tail)
            for ee in Gsp.edges:
                if (ee.tail in W or ee.tail==priodict[p]) and (ee.head not in W):
                    Gsp.remove_edge(ee)
        elif (p%2==1 and counterplayer==True) or (p%2==0 and counterplayer==False):
            U = {priodict[p]}  # vertices with path to r
            stack = [priodict[p]]
            while len(stack) > 0:  # bfs what can reach t
                current_vertex = stack.pop(0)
                E = current_vertex.incidence
                for e in E:
                    if e.head == current_vertex:
                        if e.tail not in U:
                            stack.append(e.tail)
                            U.add(e.tail)
            for ee in Gsp.edges:
                if (ee.tail in U and ee.tail != priodict[p]) and (ee.head not in U):
                    Gsp.remove_edge(ee)
    #preprocessing is done, now find shortest paths to t
    targetvertex.set_path(counterplayer, [[],0])
    #calculate shortest paths by Bellman-Ford
    for i in range(len(Gsp.vertices)):
        for eee in Gsp.edges:
            if counterplayer:
                othervalue = [list(eee.head.valuation0[1]), eee.head.valuation0[2]+0]
            else:
                othervalue = [list(eee.head.valuation1[1]), eee.head.valuation1[2]+0]
            if eee.tail.label>targetvertex.label:
                othervalue[0].append(eee.tail.label)
                othervalue[0].sort()
                othervalue[0]=othervalue[0][::-1]
            othervalue[1]+=1
            if counterplayer:
                if (eee.tail.valuation0[1:3]==[[],-1] or distance_greater(eee.tail.valuation0[1:3],othervalue,targetvertex.label)) and eee.head.valuation0[1:3]!=[[],-1]:
                    eee.tail.set_path(counterplayer, othervalue)
            else:
                if (eee.tail.valuation1[1:3]==[[],-1] or distance_greater(othervalue, eee.tail.valuation1[1:3], targetvertex.label)) and eee.head.valuation1[1:3]!=[[],-1]:
                    eee.tail.set_path(counterplayer, othervalue)
    return



def distance_greater(a,b, lambbda):
    #return whether a is larger than b
    #a,b are pairs of path (sorted from high to low priority) and distance, lambbda is the first component of valuation
    la=len(a[0])
    lb=len(b[0])
    greaterr=False
    for i in range(min(la,lb)):
        if a[0][i]*pow(-1,a[0][i]) > b[0][i]*pow(-1,b[0][i]):
            return True
        elif a[0][i]*pow(-1,a[0][i]) < b[0][i]*pow(-1,b[0][i]):
            return False
    if la>lb and a[0][lb]%2==0:
        return True
    elif la>lb and a[0][lb]%2==1:
        return False
    elif la<lb and b[0][la]%2==1:
        return True
    elif la<lb and b[0][la]%2==0:
        return False
    elif lambbda%2==0 and a[1]<b[1]:
        return True
    elif lambbda%2==1 and b[1]<a[1]:
        return True
    else:
        return False

def valuation(G, strat, firstplayer):
    #compute valuation for strategy strat and player firstplayer (True=player 1, False=player 0)
    global HH
    HH = makeGsigma(G, strat, firstplayer)
    a, b = decompose_scc(HH)
    c = set_lambdas(a, b, not firstplayer)
    set_shortest_paths(HH, c, not firstplayer)
    if firstplayer:
        for i in range(len(G.vertices)):
            G.vertices[i].set_lambda(False, HH.vertices[i].valuation1[0])
            G.vertices[i].set_path(False, [list(HH.vertices[i].valuation1[1]), HH.vertices[i].valuation1[2]+0])
    else:
        for i in range(len(G.vertices)):
            G.vertices[i].set_lambda(True, HH.vertices[i].valuation0[0])
            G.vertices[i].set_path(True, [list(HH.vertices[i].valuation0[1]), HH.vertices[i].valuation0[2]+0])

def symmetric_strategy_iteration(G, init0, init1):
    #symmetric strategy iteration algorithm, with initial strategies (as lists of edges) init0 and init1
    impr0=set()
    impr1=set()
    strat0=init0
    strat1=init1
    startt=True
    iters=0
    while startt or len(impr0)>0 or len(impr1)>0:
        startt=False
        iters+=1
        #update strategies
        for v in G.vertices:
            for e in v.incidence:
                if e.tail==v and v.player==False and e in impr0:
                    for ee in v.incidence:
                        if ee.tail==v and ee in strat0:
                            strat0.remove(ee)
                            strat0.add(e)
                            break
                elif e.tail == v and v.player == True and e in impr1:
                    for ee in v.incidence:
                        if ee.tail==v and ee in strat1:
                            strat1.remove(ee)
                            strat1.add(e)
                            break
        valuation(G, strat0, False)
        valuation(G, strat1, True)
        print('Iteration', iters)
        print('p0 strat: ', {(ey.tail.label,ey.head.label) for ey in strat0})
        print('p1 strat:', {(ey.tail.label,ey.head.label) for ey in strat1})
        impr0 = set()
        impr1 = set()
        for e in G.edges:
            if e.tail.label==5 and e.head.label==8:
                pass
            if e.tail.player==False:
                impp=False
                if e not in strat0:
                    h=e.head.valuation0[0]
                    t=e.tail.valuation0[0]
                    if t*pow(-1,t)<h*pow(-1,h):
                        impp=True
                    elif t==h:
                        if e.tail.label>t:
                            othervalue=[list(e.head.valuation0[1]), e.head.valuation0[2] + 1]
                            othervalue[0].append(e.tail.label)
                            othervalue[0].sort()
                            othervalue[0] = othervalue[0][::-1]
                        else:
                            othervalue = [list(e.head.valuation0[1]), e.head.valuation0[2] + 1]
                        if distance_greater(othervalue, e.tail.valuation0[1:3],t):
                            impp=True #is improving move
                    if impp and e.head.valuation1[0]==e.tail.valuation1[0]:
                        if e.tail.label==e.head.valuation1[0] and e.head.valuation1[1]==[]:
                            impr0.add(e)
                        else:
                            if e.tail.label>e.head.valuation1[0]:
                                othervalue=[list(e.head.valuation1[1]), e.head.valuation1[2] + 1]
                                othervalue[0].append(e.tail.label)
                                othervalue[0].sort()
                                othervalue[0] = othervalue[0][::-1]
                            else:
                                othervalue = [list(e.head.valuation1[1]), e.head.valuation1[2] + 1]
                            if othervalue==e.tail.valuation1[1:3]:
                                impr0.add(e) #if in optimal and improving
            else: #player 1 controlled node at the tail.
                impp=False
                if e not in strat1:
                    h=e.head.valuation1[0]
                    t=e.tail.valuation1[0]
                    if t*pow(-1,t)>h*pow(-1,h):
                        impp=True
                    elif t==h:
                        if e.tail.label>t:
                            othervalue=[list(e.head.valuation1[1]), e.head.valuation1[2] + 1]
                            othervalue[0].append(e.tail.label)
                            othervalue[0].sort()
                            othervalue[0] = othervalue[0][::-1]
                        else:
                            othervalue = [list(e.head.valuation1[1]), e.head.valuation1[2] + 1]
                        if distance_greater(e.tail.valuation1[1:3], othervalue,t):
                            impp=True #is improving move
                    if impp and e.head.valuation0[0]==e.tail.valuation0[0]:
                        if e.tail.label==e.head.valuation0[0] and e.head.valuation0[1]==[]:
                            impr1.add(e)
                        else:
                            if e.tail.label>e.head.valuation0[0]:
                                othervalue=[list(e.head.valuation0[1]), e.head.valuation0[2] + 1]
                                othervalue[0].append(e.tail.label)
                                othervalue[0].sort()
                                othervalue[0] = othervalue[0][::-1]
                            else:
                                othervalue = [list(e.head.valuation0[1]), e.head.valuation0[2] + 1]
                            if othervalue==e.tail.valuation0[1:3]:
                                impr1.add(e) #if in optimal and improving
        #remove extra edges
        for v in G.vertices:
            if v.player==False:
                g1={e for e in v.incidence if e.tail==v}
                if len(g1.intersection(impr0))>1:
                    g=list(g1.intersection(impr0))
                    for i in range(1,len(g)):
                        impr0.remove(i)
            else:
                g1 = {e for e in v.incidence if e.tail == v}
                if len(g1.intersection(impr1)) > 1:
                    g = list(g1.intersection(impr1))
                    for i in range(1, len(g)):
                        impr1.remove(i)
    print('Symmetric strategy improvement required ', iters,' iterations.')
    return strat0, strat1

def makeGsigma(G,strat,stratplayer):
    #construct subgraph G_sigma
    H=Graph(True, 0, False)
    for v in G.vertices:
        vert=Vertex(H, v.label, v.player, v.index)
        H.add_vertex(vert)
    for e in G.edges:
        if e.tail.player==stratplayer:
            if e in strat:
                H.add_edge(Edge(H.vertices[e.tail.index], H.vertices[e.head.index]))
        else:
            H.add_edge(Edge(H.vertices[e.tail.index], H.vertices[e.head.index]))
    return H

def create_phicounter(n):
    #create exponential counterexample for symmetric strategy iteration
    global G
    init0=set()
    init1=set()
    G=Graph(True, 0, False)
    x=Vertex(G, 1, False, 0)
    G.add_vertex(x)
    e=Edge(x,x)
    G.add_edge(e)
    init0.add(e)
    y=Vertex(G, 2, True, 1)
    G.add_vertex(y)
    e=Edge(y,y)
    G.add_edge(e)
    init1.add(e)
    r0f = Vertex(G, 3, False, 2)
    G.add_vertex(r0f)
    r1f = Vertex(G, 4, True, 3)
    G.add_vertex(r1f)
    r00=r0f
    r11=r1f
    r0=r0f
    r1=r1f
    for i in range(2,n+1):
        r0=Vertex(G, 2*i+1, False, 2*i)
        G.add_vertex(r0)
        r1=Vertex(G, 2*i+2, True, 2*i+1)
        G.add_vertex(r1)
        G.add_edge(Edge(r0, r0f))
        G.add_edge(Edge(r1,r1f))
        G.add_edge(Edge(r00,r1))
        e=Edge(r00, r0)
        G.add_edge(e)
        init0.add(e)
        e=Edge(r11, r1)
        G.add_edge(e)
        init1.add(e)
        G.add_edge(Edge(r11, r0))
        r00=r0
        r11=r1
    G.add_edge(Edge(r0, y))
    e=Edge(r0, x)
    G.add_edge(e)
    init0.add(e)
    e=Edge(r1, y)
    G.add_edge(e)
    init1.add(e)
    G.add_edge(Edge(r1, x))
    return init0, init1

# Press the green button in the gutter to run the script.
if __name__ == '__main__':
    n=4
    init0, init1=create_phicounter(n)
    print(G)
    s0,s1 = symmetric_strategy_iteration(G, init0, init1)
    print('Player 0 valuation:')
    for v in G.vertices:
        print(v.valuation0)
    print('Player 1 valuation')
    for v in G.vertices:
        print(v.valuation1)

# See PyCharm help at https://www.jetbrains.com/help/pycharm/
