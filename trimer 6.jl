using Profile,StatProfilerHTML,DataStructures,Graphs,GraphPlot,Compose,Cairo

mutable struct Lit
    coef::Int
    sign::Bool
    var::Int
end
mutable struct Eq
    t::Vector{Lit}
    b::Int
end
function readvar(s,varmap)
    tmp = split(s,'~')[end]
    for i in eachindex(varmap)
        if varmap[i]==tmp
            return i
        end
    end
    push!(varmap,tmp)
    return length(varmap)
end
function readeq(st,varmap)
    return readeq(st,varmap,1:2:length(st)-3)
end
function readeq(st,varmap,range)
    lits = Vector{Lit}(undef,(length(range)))
    for i in range
        coef = parse(Int,st[i])
        sign = st[i+1][1]!='~'
        var = readvar(st[i+1],varmap)
        lits[(i - range.start)÷range.step+1] = Lit(coef,sign,var)
    end
    eq = Eq(lits,parse(Int,st[end-1]))
    return eq
end
function removespaces(st)
    r = findall(x->x=="",st)
    deleteat!(st,r)
end
function readopb(path,file)
    system = Eq[]
    varmap = String[]
    open(string(path,'/',file,".opb"),"r"; lock = false) do f
        for ss in eachline(f)
            if ss[1] != '*'                                     #do not parse comments
                st = split(ss,' ')                              #structure of line is: int var int var ... >= int ; 
                removespaces(st)
                eq = readeq(st,varmap)
                if length(eq.t)==0 && eq.b==1
                    printstyled(" !opb"; color = :blue)
                end
                normcoefeq(eq)
                push!(system, eq)
            end
        end
    end
    return system,varmap
end
function normlit(l)
    if !l.sign
        return Lit(-l.coef,true,l.var),l.coef
    end
    return l,0
end
function normcoef(l)
    if l.coef<0
        l.coef = -l.coef
        l.sign = !l.sign
        return l.coef
    end
    return 0
end
function normcoefeq(eq)
    c=0
    for l in eq.t
        c+= normcoef(l)
    end
    eq.b = c+eq.b
end
function normcoefsystem(s)
    for eq in s
        normcoefeq(eq)
    end
end
function add(lit1,lit2)
    lit1,c1 = normlit(lit1)
    lit2,c2 = normlit(lit2)
    return Lit(lit1.coef+lit2.coef,true,lit1.var),c1+c2
end
function removenulllits(lits)
    return [l for l in lits if l.coef!=0]
end
function addeq(eq1,eq2)
    lits = copy(eq2.t)
    vars = [l.var for l in lits]
    c = 0
    for lit in eq1.t
        i = findfirst(x->x==lit.var,vars)
        if !isnothing(i)
            tmplit,tmpc = add(lit,lits[i])
            lits[i] = tmplit
            c+=tmpc
        else
            push!(lits,lit)
        end
    end
    lits=removenulllits(lits)
    # lits=sort(lits,lt=islexicolesslit)                          # optionnal sorting of literrals
    return Eq(lits,eq1.b+eq2.b-c)
end
function multiply(eq,d)
    lits = copy(eq.t)
    for l in lits
        l.coef = l.coef*d
    end
    return Eq(lits,eq.b*d)
end
function divide(eq,d)
    lits = copy(eq.t)
    for l in lits
        l.coef = ceil(Int,l.coef/d)
    end
    return Eq(lits,ceil(Int,eq.b/d))
end
function saturate(eq)
    for l in eq.t
        l.coef = min(l.coef,eq.b)
    end
end
function copyeq(eq)
    return Eq([Lit(l.coef,l.sign,l.var) for l in eq.t], eq.b)
end
function solvepol(st,system,link)
    id = parse(Int,st[2])
    eq = copyeq(system[id])
    stack = Stack{Eq}()
    push!(stack,eq)
    push!(link,id)
    for j in 3:length(st)
        i=st[j]
        if i=="+"
            push!(stack,addeq(pop!(stack),pop!(stack)))     
            push!(link,-1)
        elseif i=="*"
            push!(stack,multiply(pop!(stack),link[end]))
            push!(link,-2)
        elseif i=="d"
            push!(stack,divide(pop!(stack),link[end]))
            push!(link,-3)
        elseif i=="s"
            normcoefeq(first(stack))
            saturate(first(stack))
            push!(link,-4)
        elseif i=="w"
            printstyled(" !weak"; color = :blue)
        elseif i!="0"
            id = parse(Int,i)
            push!(link,id)
            if !(st[j+1] in ["*","d"])
                push!(stack,copyeq(system[id]))    
            end
        end
    end
    eq = pop!(stack)
    lits = eq.t
    lits2 = removenulllits(lits)
    if length(link)==2
        link[1] = -3
    end
    return Eq(lits2,eq.b)
end
function findfullassi(system,st,init,varmap)
    isassi,assi = initassignement(varmap)
    lits = Vector{Lit}(undef,length(st)-1)
    for i in 2:length(st)
        sign = st[i][1]!='~'
        var = readvar(st[i],varmap)
        lits[i-1] = Lit(1,!sign,var)
        assi[var] = sign
        isassi[var] = true
    end
    changes = true
    while changes
        changes = false
        for i in 1:init-1
            eq = system[i]
            s = slack(eq,assi)
            if s<0
                printstyled(" !sol"; color = :red)
                print(" ",i," ")
                printeq(eq)
                lits = [Lit(l.coef,!l.sign,l.var) for l in lits]
                return Eq(lits,1)
            else
                for l in eq.t
                    if !isassi[l.var] && l.coef > s
                        assi[l.var] = l.sign
                        isassi[l.var] = true 
                        changes = true
                    end
                end
            end
        end
    end

    lits = Vector{Lit}(undef,sum(isassi))
    j=1
    for i in findall(isassi)
        lits[j] = Lit(1,!assi[i],i)
        j+=1
    end
    eq = Eq(lits,1)
    if sum(isassi)!=length(isassi)
        printstyled(" !FA"; color = :blue)
        printeq(eq)
    end
    return eq
end
function readred(st,varmap,redwitness,c)
    i = findfirst(x->x==";",st)
    eq = readeq(st[2:i],varmap)
    redwitness[c] = join(st[i+1:end]," ")
    return eq
end
function readveripb(path,file,system,varmap)
    systemlink = Vector{Int}[]
    redwitness = Dict{Int, String}()
    com = Dict{Int, String}()
    output = conclusion = ""
    c = length(system)
    open(string(path,'/',file,extention),"r"; lock = false) do f
        c+=1
        for ss in eachline(f)
            st = split(ss,' ')
            type = st[1]
            removespaces(st)
            eq = Eq([],0)
            if type == "u" || type == "rup"
                eq = readeq(st,varmap,2:2:length(st)-3)     # can fail is space is missing omg
                push!(systemlink,[-1])
            elseif type == "p" || type == "pol"
                push!(systemlink,[-2])
                eq = solvepol(st,system,systemlink[end])
            elseif type == "ia"
                push!(systemlink,[-3,parse(Int,st[end])])
                eq = readeq(st[1:end-1],varmap,2:2:length(st)-4)
            elseif type == "red"  
                push!(systemlink,[-4])
                eq = readred(st,varmap,redwitness,c)
            elseif type == "sol" || type == "soli"         # on ajoute la negation au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                push!(systemlink,[-5])
                eq = findfullassi(system,st,c,varmap)
            elseif type == "output"
                output = st[2]
            elseif type == "conclusion"
                conclusion = st[2]
            elseif type == "*trim"
                com[length(system)+1] = ss[7:end]
            elseif !(ss[1:2] in ["# ","w ","ps","* ","f ","d ","de","co","en"])
                println("unknown: ",ss)
            end
            if length(eq.t)!=0 || eq.b!=0
                normcoefeq(eq)
                push!(system,eq)
            end
        end
    end
    return system,systemlink,redwitness,output,conclusion,com,version
end
function slack(eq::Eq,assi::Vector{Int8})
    c=0
    for l in eq.t
        if assi[l.var] == 0 || 
            (l.sign && assi[l.var] == 1) || 
            (!l.sign && assi[l.var] == 2) 
            c+=l.coef
        end
    end
    if length(eq.t) > 0
        c-= eq.b
    end
    return c
end
function reverse(eq::Eq)
    c=0
    lits = [Lit(l.coef,l.sign,l.var) for l in eq.t]
    for l in lits
        l.sign = !l.sign
        c+=l.coef
    end
    return Eq(lits,-eq.b+1+c)
end
function fixante(systemlink::Vector{Vector{Int}},antecedants::Vector{Bool},i)
    for j in eachindex(systemlink[i])
        t = systemlink[i][j]
        if t>0 && !(j<length(systemlink[i]) && (systemlink[i][j+1] == -2 || systemlink[i][j+1] == -3))
            antecedants[t] = true
        end
    end
end
function fixfront(front::Vector{Bool},antecedants::Vector{Bool})
    for i in eachindex(antecedants)
        if antecedants[i]
            front[i] = true
        end
    end
end
function fixfront(front::Vector{Bool},antecedants::Vector{Int})
    for i in antecedants
        if i>0
            front[i] = true
        end
    end
end
function makesmol(system,invsys,varmap,systemlink,nbopb)
    n = length(system)
    antecedants = zeros(Bool,n)
    assi = zeros(Int8,length(varmap))
    cone = zeros(Bool,n)
    cone[end] = true
    front = zeros(Bool,n)
    firstcontradiction = findfirst(x->length(x.t)==0,system)
    cone[firstcontradiction] = true
    if systemlink[firstcontradiction-nbopb][1] == -2         # pol case
        fixfront(front,systemlink[firstcontradiction-nbopb])
    else

        # @time updumb(system,assi,front)                     #front now contains the antecedants of the final claim
        # println("  init : ",sum(front))#,findall(front)

        # front = zeros(Bool,n)
        # assi = zeros(Int8,length(varmap))
        # @time upque(system,invsys,assi,front)                     #front now contains the antecedants of the final claim
        # println("  init : ",sum(front))#,findall(front)

        # front = zeros(Bool,n)
        # assi = zeros(Int8,length(varmap))
        @time upquebit(system,invsys,assi,front)
        println("  init : ",sum(front))#,findall(front)

        append!(systemlink[firstcontradiction-nbopb],findall(front))
    end
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                tlink = systemlink[i-nbopb][1]
                if tlink == -1 
                    antecedants .=false ; assi.=0
                    rup(system,invsys,antecedants,i,assi,front,cone)
                    # rupque(system,invsys,antecedants,i,assi,front,cone) # la rupque est moins efficace pour le trimmer mais elle fais de plus petites preuves
                    append!(systemlink[i-nbopb],findall(antecedants))
                    fixfront(front,antecedants)
                elseif tlink >= -3
                    antecedants .= false
                    fixante(systemlink,antecedants,i-nbopb)
                    fixfront(front,antecedants)
                end
            end
        end
    end
    return cone
end
function updateque(eq,que,invsys,s,i,assi::Vector{Int8},antecedants)
    sset = SortedSet{Int}(Base.Order.Reverse)
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            for id in invsys[l.var]
                push!(sset,id)  
            end
        end
    end
    for i in sset
        push!(que,i)
    end
end
function fillprioque(invsys,l,init,cone,front,prioque,que)
    for id in invsys[l.var]
        if id<=init
            if cone[id] || front[id]
                pushfirst!(prioque,id)
            else
                pushfirst!(que,id)  
end end end end
function updateprioque(eq,prioque,que,invsys,cone,front,s,i,init,assi::Vector{Int8},antecedants)
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            fillprioque(invsys,l,init,cone,front,prioque,que)
end end end
function addinvsys(invsys,eq,id)
    for l in eq.t
        if !isassigned(invsys,l.var)
            invsys[l.var] = [id]
        else
            push!(invsys[l.var],id)
        end
    end
end
function getinvsys(system,varmap)
    invsys = Vector{Vector{Int}}(undef,length(varmap))
    for i in eachindex(system)
        addinvsys(invsys,system[i],i)
    end # arrays should be sorted at this point
    return invsys
end
function update(eq,s,i,assi,antecedants)
    changes = false
    for l in eq.t
        if assi[l.var]==0 && l.coef > s
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            changes = true
        end
    end
    return changes
end
# cque = [31336, 31344, 31346, 31364, 18926, 31366, 1319, 31412, 31424, 21062, 31426, 21044, 31456, 31464, 31472, 31474, 31492, 24266, 31494, 1884, 31544, 31576, 31578, 31338, 31348, 18670, 31350, 18556, 18594, 18632, 31352, 18706, 31354, 1325, 31414, 31420, 20842, 31422, 20824, 31458, 31466, 31476, 24010, 31478, 23896, 23934, 2165, 31584, 31484, 31486, 31508, 24546, 31510, 1899, 707, 6887, 709, 6892, 31356, 31358, 31380, 19206, 31382, 1329, 142, 1412, 31600, 9472, 28538, 9477, 31602, 28520, 31636, 31638, 31670, 31368, 18978, 31370, 1323, 31428, 21114, 31430, 21088, 31496, 24318, 31498, 2168, 31580, 31480, 24046, 31482, 1893, 31540, 31582, 31488, 24230, 31490, 24092, 24138, 24184, 31516, 24650, 31518, 1896, 695, 6857, 697, 6862, 31360, 18890, 31362, 18752, 18798, 18844, 31388, 19310, 31390, 1327, 130, 1418, 31596, 9442, 28318, 9447, 31598, 28300, 31632, 31634, 31688, 31690, 31724, 31726, 31762, 31770, 31440, 21446, 31442, 21424, 31560, 2173, 31588, 31342, 31396, 31398, 31408, 19586, 31410, 1343, 31418, 31452, 21722, 31454, 21704, 31462, 31470, 31524, 31526, 31536, 24926, 31538, 1920, 31572, 31592, 31340, 31392, 19386, 31394, 19348, 19424, 19462, 31400, 19498, 31402, 1339, 31416, 31444, 21634, 31446, 21616, 31460, 31468, 31520, 24726, 31522, 24688, 24764, 24802, 2189, 31594, 31628, 29198, 31630, 29180, 31664, 31666, 31680, 731, 733, 751, 753, 824, 826, 844, 846, 31376, 31378, 1337, 166, 1420, 31616, 9532, 28922, 9537, 31618, 28900, 31652, 31654, 31708, 31710, 31744, 31746, 186, 1436, 31684, 31404, 19550, 31406, 1341, 31448, 21686, 31450, 21660, 31532, 24890, 31534, 2186, 31590, 31528, 24838, 31530, 1914, 31564, 2185, 31586, 440, 22410, 442, 22388, 31500, 31502, 1905, 723, 6927, 9277, 2175, 31608, 28818, 6462, 6932, 31610, 28796, 31644, 31646, 31692, 31694, 31700, 31702, 31728, 31730, 31736, 31738, 2269, 31768, 2404, 743, 6977, 745, 6982, 31372, 19070, 31374, 1321, 17815, 17830, 17875, 31720, 9582, 31722, 9587, 31756, 31758, 31774, 31504, 24502, 31506, 1887, 687, 3782, 4252, 6837, 9422, 689, 1743, 14527, 16642, 3787, 1647, 4257, 6842, 9427, 691, 3792, 4262, 6847, 9197, 2402, 13132, 14542, 16657, 9432, 20806, 1651, 31548, 2263, 31604, 28590, 31606, 28564, 31640, 31642, 31696, 31698, 31732, 31734, 2401, 1653, 4267, 1747, 6382, 6852, 9437, 735, 3902, 4372, 6957, 9542, 737, 1773, 14577, 15752, 16692, 31620, 2747, 1432, 31622, 9567, 29092, 9562, 31656, 31658, 31712, 31714, 31748, 31750, 29110, 3907, 1667, 4377, 6962, 9547, 2467, 739, 3912, 4382, 6967, 9552, 21598, 1669, 31568, 2281, 31624, 29162, 31626, 29136, 31660, 31662, 31716, 31718, 31752, 31754, 2410, 1671, 13177, 14587, 16702, 4387, 1774, 6502, 6972, 9557, 2166, 17345, 2182, 17405, 2260, 2276, 2353, 2361, 24364, 24410, 2179, 17395, 2273, 2406, 24456, 2400, 2408, 1333, 158, 1422, 9512, 1415, 1427, 1509, 2448, 2460, 9515, 19024, 19116, 19162, 1430, 2359, 2363, 1435, 2468, 19524, 2464, 2267, 2403, 2454, 2356, 2354, 1417, 2450, 18952, 2456, 2357, 31384, 2712, 3887, 4357, 9527, 21372, 22440, 31386, 1331, 10337, 11042, 432, 4322, 9492, 434, 1661, 12682, 654, 655, 4327, 9497, 436, 4332, 9502, 21298, 1663, 17857, 1301, 4337, 1666, 12692, 658, 659, 1765, 656, 5812, 9572, 657, 5817, 9577, 31512, 2707, 1334, 10325, 11032, 416, 4282, 9452, 418, 1657, 12672, 636, 637, 644, 645, 4287, 9457, 420, 4292, 4062, 1649, 12652, 626, 627, 628, 629, 640, 641, 642, 643, 650, 651, 652, 653, 714, 716, 718, 720, 1655, 12667, 630, 631, 648, 649, 12442, 539, 1759, 632, 5692, 633, 5697, 634, 5702, 9462, 635, 5707, 9467, 638, 5722, 9482, 639, 5727, 9487, 646, 5762, 5532, 5767, 1900, 792, 794, 2038, 1059, 8767, 1060, 8772, 796, 798, 2035, 1053, 8737, 1054, 8742, 804, 806, 2029, 14567, 13392, 808, 810, 2044, 1067, 8807, 1068, 8812, 1077, 8857, 1078, 8862, 812, 814, 2026, 1049, 8717, 1050, 8722, 1051, 8727, 1052, 8732, 1063, 1064, 1110, 1111, 2050, 1065, 1066, 1071, 8827, 1072, 8832, 1081, 8877, 1082, 8882, 1112, 1113, 820, 9522, 2459, 14557, 823, 7647, 2176, 15732, 15037, 1229, 1232, 2275, 16682, 17387, 31612, 28878, 31614, 28848, 31648, 31650, 31704, 31706, 31740, 31742, 17140, 17377, 6985, 8402, 6757, 2056, 1073, 8837, 1074, 8842, 1075, 8847, 1076, 8852, 1079, 8867, 1127, 8345, 8817, 8350, 8822, 8275, 8747, 8280, 8752, 8285, 8757, 8290, 8762, 8305, 8777, 8547, 8782, 32016, 33005, 1409, 27062, 1411, 27044, 2536, 2538, 33994, 1365, 26402, 1367, 26384, 2492, 2494, 34968, 1345, 1347, 96, 3717, 9357, 1349, 26146, 1351, 26032, 26070, 26108, 1545, 1548, 1551, 28282, 1554, 382, 384, 478, 28168, 28206, 28244, 2472, 2474, 2476, 2478, 36041, 1377, 1379, 1471, 1473, 1593, 1596, 396, 499, 2504, 2506, 2577, 3752, 4222, 9392, 2597, 3772, 4242, 9412, 37015, 1393, 1395, 1397, 26938, 1399, 120, 3777, 9417, 26824, 26862, 26900, 1405, 27026, 1407, 27000, 1617, 1620, 398, 1623, 29074, 1626, 28960, 28998, 29036, 2520, 2522, 2524, 2526, 2532, 2534, 38076, 1357, 1359, 1369, 26454, 1371, 100, 9367, 26428, 1385, 26742, 1387, 26712, 1451, 1453, 1563, 1566, 388, 487, 2484, 2486, 2496, 2498, 2512, 2514, 2562, 3737, 4207, 9377, 39065, 3, 53, 39559, 208, 30, 394, 2582, 4227, 9397, 39560, 1360, 1372, 26546, 1374, 26500, 1454, 1805, 1945, 2086, 2206, 2300, 2373, 2420, 2489, 2501, 2503, 5372, 6077, 1782, 1785, 613, 1788, 1791, 616, 7492, 2198, 30454, 2200, 30436, 2369, 2370, 1921, 1924, 848, 6782, 1928, 1931, 856, 2190, 2192, 2194, 30418, 2196, 1139, 2416, 2417, 8197, 8667, 30304, 30342, 30380, 2214, 30726, 2216, 1136, 2309, 2414, 2415, 2424, 2425, 8192, 2069, 2072, 8662, 2365, 2366, 2367, 2368, 2377, 2378, 2062, 2065, 1036, 1083, 27410, 27412, 27414, 27416, 9980, 10687, 18442, 25614, 106, 1476, 18447, 1276, 10030, 10507, 10037, 116, 1494, 18022, 18260, 1281, 39067, 2234, 31058, 2236, 31036, 2387, 2388, 2434, 2435, 40003, 7, 55, 5, 40031, 1, 52, 23, 25504, 25718, 25506, 25696, 39068, 40045, 25, 67, 27, 40051, 47, 40053, 492, 34, 620, 5632, 5387]
# sum(cque) = 12_408_975  
# cdumb = [31336, 31338, 31340, 31342, 31344, 31346, 31348, 18670, 31350, 18556, 18594, 18632, 31352, 18706, 31354, 1325, 1419, 1515, 2452, 18688, 31356, 31358, 31360, 18890, 31362, 18752, 18798, 18844, 31364, 18926, 31366, 1319, 1413, 1506, 2446, 18908, 31368, 18978, 31370, 1323, 1417, 1512, 2450, 18952, 31372, 31374, 31376, 19162, 31378, 19024, 19070, 19116, 31380, 19206, 31382, 1329, 1423, 1521, 424, 426, 541, 544, 2456, 1294, 1295, 19184, 31384, 19266, 31386, 1331, 1425, 1524, 428, 430, 547, 550, 2458, 1296, 1297, 19236, 31388, 19310, 31390, 1327, 1421, 1518, 412, 414, 523, 526, 2454, 1288, 1289, 19288, 31392, 31394, 31396, 19462, 31398, 1321, 1415, 1509, 404, 406, 408, 410, 416, 418, 420, 422, 511, 514, 517, 520, 529, 532, 535, 538, 1647, 1651, 1653, 1741, 1747, 1750, 2448, 1284, 1285, 1286, 1287, 1290, 1291, 1292, 1293, 19348, 19386, 19424, 31400, 2752, 3927, 4397, 9567, 21616, 22684, 31402, 1333, 1339, 178, 1426, 1432, 1527, 440, 442, 565, 568, 1536, 1657, 1756, 636, 637, 706, 708, 2460, 1302, 1303, 2466, 1312, 31404, 2762, 3937, 4407, 9577, 21660, 22728, 31406, 1335, 1341, 182, 1428, 1434, 1530, 432, 434, 444, 446, 553, 556, 571, 574, 1539, 452, 454, 583, 586, 1659, 1661, 1667, 1759, 638, 639, 710, 712, 1762, 644, 645, 722, 724, 1771, 654, 655, 742, 744, 2462, 1298, 1299, 1304, 1305, 2468, 1308, 1309, 1314, 31408, 2772, 3947, 4417, 9587, 21704, 22772, 31410, 1337, 1343, 186, 1430, 1436, 1533, 436, 438, 448, 450, 559, 562, 577, 580, 1542, 456, 458, 589, 592, 1649, 1655, 1663, 1665, 1669, 1671, 1744, 626, 627, 628, 629, 632, 633, 686, 688, 690, 692, 698, 700, 1753, 630, 631, 634, 635, 694, 696, 702, 704, 1765, 640, 641, 646, 647, 714, 716, 726, 728, 1768, 642, 643, 648, 649, 718, 720, 730, 732, 1774, 650, 651, 656, 657, 734, 736, 746, 748, 1777, 652, 653, 658, 659, 738, 740, 750, 752, 1882, 1885, 1888, 780, 782, 900, 904, 1891, 784, 786, 908, 912, 1894, 788, 790, 916, 920, 1897, 800, 802, 940, 944, 1900, 792, 794, 796, 798, 804, 806, 924, 928, 932, 936, 948, 952, 1903, 816, 818, 972, 976, 1906, 808, 810, 820, 822, 956, 960, 980, 984, 1909, 812, 814, 824, 826, 964, 968, 988, 992, 1912, 836, 838, 1012, 1016, 1915, 828, 830, 840, 842, 996, 1000, 1020, 1024, 1918, 832, 834, 844, 846, 1004, 1008, 1028, 1032, 2023, 2026, 2029, 1049, 1050, 1096, 1097, 2032, 1051, 1052, 1098, 1099, 2035, 1053, 1054, 1100, 1101, 2038, 1059, 1060, 1106, 1107, 2041, 1055, 1056, 1057, 1058, 1061, 1062, 1102, 1103, 1104, 1105, 1108, 1109, 2044, 1067, 1068, 1114, 1115, 2047, 1063, 1064, 1069, 1070, 1110, 1111, 1116, 1117, 2050, 1065, 1066, 1071, 1072, 1112, 1113, 1118, 1119, 2053, 1077, 1078, 1124, 1125, 2056, 1073, 1074, 1079, 1080, 1120, 1121, 1126, 1127, 2059, 1075, 1076, 1081, 1082, 1122, 1123, 1128, 1129, 2164, 2166, 2168, 1169, 1172, 2170, 1175, 1178, 2172, 1181, 1184, 2174, 1199, 1202, 2176, 1187, 1190, 1193, 1196, 1205, 1208, 2178, 1223, 1226, 2180, 1211, 1214, 1229, 1232, 2182, 1217, 1220, 1235, 1238, 2184, 1253, 1256, 2186, 1241, 1244, 1259, 1262, 2188, 1247, 1250, 1265, 1268, 2258, 2260, 2262, 2264, 2266, 2268, 2270, 2272, 2274, 2276, 2278, 2280, 2282, 2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2399, 2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2464, 1300, 1301, 1306, 1307, 2470, 1310, 1311, 1316, 31412, 31414, 31416, 31418, 31456, 31458, 31460, 31462, 31464, 31466, 31468, 31470, 31596, 28318, 31598, 28300, 31600, 28538, 31602, 28520, 31604, 28590, 31606, 28564, 31608, 28818, 31610, 28796, 31612, 28878, 31614, 28848, 31616, 28922, 31618, 28900, 31620, 29110, 31622, 29092, 31624, 29162, 31626, 29136, 31628, 29198, 31630, 29180, 31632, 31634, 31636, 31638, 31640, 31642, 31644, 31646, 31648, 31650, 31652, 31654, 31656, 31658, 31660, 31662, 31664, 31666, 31688, 31690, 31692, 31694, 31696, 31698, 31700, 31702, 31704, 31706, 31708, 31710, 31712, 31714, 31716, 31718, 31720, 31722, 31724, 31726, 31728, 31730, 31732, 31734, 31736, 31738, 31740, 31742, 31744, 31746, 31748, 31750, 31752, 31754, 31756, 31758, 32016, 33005, 1409, 1411, 1503, 1505, 2536, 2538, 33994, 1365, 1367, 1459, 1461, 2492, 2494, 34968, 1345, 1347, 96, 1349, 1351, 1439, 1441, 1443, 1445, 1545, 1548, 378, 1551, 1554, 382, 384, 478, 2472, 2474, 1271, 2476, 2478, 28168, 28206, 28244, 28282, 36041, 1377, 1379, 1471, 1473, 1593, 1596, 396, 499, 2504, 2506, 2577, 2597, 3752, 3772, 4222, 4242, 9392, 9412, 37015, 1393, 1395, 1397, 1399, 120, 1405, 1407, 1487, 1489, 1491, 1493, 1499, 1501, 1617, 1620, 398, 1623, 1626, 402, 2520, 2522, 2524, 2526, 1283, 2532, 2534, 28960, 28998, 29036, 29074, 38076, 1357, 1359, 1369, 1371, 100, 1385, 1387, 1451, 1453, 1463, 1465, 1479, 1481, 1563, 1566, 388, 487, 2484, 2486, 2496, 2498, 1273, 2512, 2514, 2562, 3737, 4207, 9377, 39065, 3, 53, 1373, 1375, 112, 1381, 1383, 106, 1401, 1403, 116, 1467, 1469, 1474, 1476, 1494, 1496, 1587, 1590, 394, 496, 2500, 2502, 1279, 2508, 2510, 1276, 2528, 2530, 1281, 28636, 28682, 28728, 28774, 39067, 1805, 1808, 1945, 1948, 2086, 2089, 2198, 2200, 2206, 2208, 2234, 2236, 2292, 2294, 2300, 2302, 2328, 2330, 2369, 2370, 2373, 2374, 2387, 2388, 2416, 2417, 2420, 2421, 2434, 2435, 5372, 1787, 1790, 6077, 1782, 1785, 613, 1921, 1924, 848, 1927, 1930, 758, 856, 2062, 2065, 1036, 1083, 2068, 2071, 1038, 1085, 2190, 2192, 2194, 2196, 2214, 2216, 1136, 2284, 2286, 2288, 2290, 2308, 2310, 2365, 2366, 2367, 2368, 2377, 2378, 2414, 2415, 2424, 2425, 39559, 29, 71, 25252, 98, 108, 1454, 39560, 2489, 40003, 7, 55, 5, 1822, 1825, 620, 674, 1828, 1831, 621, 676, 1852, 1855, 623, 1858, 1861, 624, 625, 9, 54, 11, 60]
# sum(cdumb) = 6_932_430 
function updumb(system,assi,antecedants) 
    changes = true
    while changes
        changes = false
        i = 0
        while !changes && i<=length(system)
            i+=1
        # for i in eachindex(system)
            eq = system[i]
            s = slack(eq,assi)
            if s<0
                antecedants[i] = true
                return 
            else
                changes |= update(eq,s,i,assi,antecedants)
                if changes print(i,", ") end
            end
        end
    end
    printstyled(" updumb Failed "; color = :red)
end
function upque(system,invsys,assi,antecedants)
    que = Deque{Int}()
    for id in eachindex(system)
        pushfirst!(que,id) end
    while !isempty(que)
        i = pop!(que)
        eq = system[i]
        s = slack(eq,assi)
        if s<0
            antecedants[i] = true
            return 
        else
            ln = length(que)
            updateque(eq,que,invsys,s,i,assi,antecedants)
            if ln<length(que) print(i,", ") end
        end
    end
    printstyled(" upQue empty "; color = :red)
end
function updatequebit(eq,que,invsys,s,i,assi::Vector{Int8},antecedants)
    rewind = i+1
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            for id in invsys[l.var]
                rewind = min(rewind,id)
                que[id] = true
            end
        end
    end
    return rewind
end
function upquebit(system,invsys,assi,antecedants)
    que = ones(Bool,length(system))
    i = 1
    while i<=length(system)
        if que[i]
            eq = system[i]
            s = slack(eq,assi)
            if s<0
                antecedants[i] = true
                return 
            else
                rewind = updatequebit(eq,que,invsys,s,i,assi,antecedants)
                que[i] = false
                i = min(i,rewind-1)
            end
        end
        i+=1
    end
    printstyled(" upQueBit empty "; color = :red)
end
function updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi::Vector{Int8},antecedants)
    rewindcone = rewindfront = rewind = init+1
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            for id in invsys[l.var]
                if id<i
                    que[id] = true
                    rewind = min(rewind,id)
                    if cone[id]
                        rewindcone = min(rewindcone,id)
                    end
                    if front[id]
                        rewindfront = min(rewindfront,id)
                    end
                end
            end
        end
    end
    return rewind,rewindfront,rewindcone
end
function rup(system,invsys,antecedants,init,assi,front,cone)
    que = ones(Bool,init)
    rev = reverse(system[init])
    i = 1
    prio = 2
    while i<=init && prio>=0
        r0 = r1 = r2 = init+1
        if que[i]
            if prio == 2
                if cone[i]
                    printstyled(string(i," "); color = :yellow)
                    eq = i==init ? rev : system[i]
                    s = slack(eq,assi)
                    if s<0
                        antecedants[i] = true
                        return
                    else
                    r0,r1,r2 = updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi,antecedants)
                    end
                    que[i] = false
                end
            elseif prio == 1
                if front[i]
                    printstyled(string(i," "); color = :green)
                    eq = i==init ? rev : system[i]
                    s = slack(eq,assi)
                    if s<0
                        antecedants[i] = true
                        return
                    else
                    r0,r1,r2 = updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi,antecedants)
                    end
                    que[i] = false
                end
            else
                printstyled(string(i," "); color = :blue)
                eq = i==init ? rev : system[i]
                s = slack(eq,assi)
                if s<0
                    antecedants[i] = true
                    return
                else
                r0,r1,r2 = updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi,antecedants)
                end
                que[i] = false
            end
        end
        i+=1
        if r2<=init
            printstyled(" Rewind \n"; color = :violet)
            prio = 2
            i = r2
        elseif r1<=init
            printstyled(" Rewind \n"; color = :cyan)
            prio = 1
            i = r1
        else
            i = min(i+1,r0)
        end
        if i==init+1 
            prio-=1
            i = 1
        end
    end
    printstyled(" Rewind321 \n"; color = :violet)
    printstyled(" Rewind321 \n"; color = :cyan)

    printstyled(" rup faled \n"; color = :red)
    printstyled(" rup faled \n"; color = :red)
    printstyled(" rup faled \n"; color = :red)
    printstyled(" rup faled \n"; color = :red)
    printstyled(" rup faled \n"; color = :red)
    printstyled(" rup faled \n"; color = :red)
    printstyled(" rup faled \n"; color = :red)
end
function rupque(system::Vector{Eq},invsys,antecedants::Vector{Bool},init,assi::Vector{Int8},front::Vector{Bool},cone::Vector{Bool})
    que = Deque{Int}()
    prioque = Deque{Int}()
    for id in 1:init
        if id<=init
            pushfirst!(que,id) end end
    for i in que
        if cone[i] || front[i]
            pushfirst!(prioque,i) end end
    rev = reverse(system[init])
    while !isempty(prioque) || !isempty(que)
        i = !isempty(prioque) ? pop!(prioque) : pop!(que)
        eq = i==init ? rev : system[i]
        s = slack(eq,assi)
        if s<0
            antecedants[i] = true
            return 
        else
            updateprioque(eq,prioque,que,invsys,cone,front,s,i,init,assi,antecedants)
        end
    end
    printstyled(" rupQue empty "; color = :red)
end
function readinstance(path,file)
    system,varmap = readopb(path,file)
    nbopb = length(system)
    system,systemlink,redwitness,output,conclusion,com,version = readveripb(path,file,system,varmap)
    return system,systemlink,redwitness,nbopb,varmap,output,conclusion,com,version
end
function writelit(l,varmap)
    return string(l.coef," ",if l.sign "" else "~" end, varmap[l.var])
end
function writeeq(e,varmap)
    s = ""
    for l in e.t
        s = string(s,writelit(l,varmap)," ")
    end
    return string(s,">= ",e.b," ;\n")
end
function writeu(e,varmap)
    return string("u ",writeeq(e,varmap))
end
function writeiaold(e,link,cone,varmap)
    return string("ia ",sum(cone[1:link])," : ",writeeq(e,varmap))
end
function writeia(e,link,index,varmap)
    return string("ia ",writeeq(e,varmap)[1:end-1]," ",index[link],"\n")
end
function writesol(e,varmap)
    s = "solx"
    for l in e.t
        s = string(s,if l.sign " ~" else " " end, varmap[l.var])
    end
    return string(s,"\n")
end
function writered(e,varmap,witness)
    s = "red"
    for l in e.t
        s = string(s," ",l.coef,if !l.sign " ~" else " " end, varmap[l.var])
    end
    return string(s," >= ",e.b," ; ",witness,"\n")
end
function writepol(link,index)
    s = string("p")
    for i in 2:length(link)
        t = link[i]
        if t==-1
            s = string(s," +")
        elseif t==-2
            s = string(s," *")
        elseif t==-3
            s = string(s," d")
        elseif t==-4
            s = string(s," s")
        elseif t>0
            if link[i+1] in [-2,-3]
                s = string(s," ",t)
            else
                s = string(s," ",index[t])
            end
        end
    end
    return string(s,"\n")
end
function invlink(systemlink,succ::Vector{Vector{Int}},nbopb)
    for i in eachindex(systemlink)
        if isassigned(systemlink,i)
            t = systemlink[i]
            for j in t
                if j>0
                    if isassigned(succ,j)
                        push!(succ[j],i+nbopb)
                    else
                        succ[j] = [i+nbopb]
                    end
                end
            end
        end
    end
end
function writedel(f,systemlink,i,succ,index,nbopb,dels)
    isdel = false
    for p in systemlink[i-nbopb]
        if p>nbopb && !dels[p] 
            m = maximum(succ[p])
            if m == i
                if !isdel
                    write(f,string("del id "))
                    isdel = true
                end
                dels[p] = true
                write(f,string(index[p]," "))
            end
        end
    end
    if isdel
        write(f,string("\n"))
    end
end
function writeconedel(path,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
    index = zeros(Int,length(system))
    lastindex = 0
    open(string(path,"/smol.",file,".opb"),"w") do f
        for i in 1:nbopb
            if cone[i]
                lastindex += 1
                index[i] = lastindex
                eq = system[i]
                write(f,writeeq(eq,varmap))
            end
        end
    end
    succ = Vector{Vector{Int}}(undef,length(system))
    dels = zeros(Bool,length(system))
    invlink(systemlink,succ,nbopb)
    open(string(path,"/smol.",file,extention),"w") do f
        write(f,string("pseudo-Boolean proof version ",version,"\n"))
        write(f,string("f ",sum(cone[1:nbopb])," 0\n"))
        for i in nbopb+1:length(system)
            if cone[i]
                lastindex += 1
                index[i] = lastindex
                eq = system[i]
                tlink = systemlink[i-nbopb][1]
                if tlink == -1               # rup
                    write(f,writeu(eq,varmap))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -2           # pol
                    write(f,writepol(systemlink[i-nbopb],index))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)

                    # write(f,writeia(eq,i,index,varmap))
                    # write(f,string("del id ",lastindex,"\n"))
                    # lastindex += 1
                    # index[i] = lastindex
                elseif tlink == -3           # ia
                    write(f,writeia(eq,systemlink[i-nbopb][2],index,varmap))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -4           # red
                    write(f,writered(eq,varmap,redwitness[i]))
                elseif tlink == -5           # solx
                    write(f,writesol(eq,varmap))
                end
            end
        end
        write(f,string("output ",output,"\n"))
        if conclusion == "SAT"
            write(f,string("conclusion ",conclusion,"\n"))
        else
            write(f,string("conclusion ",conclusion," : -1\n"))
        end
        write(f,"end pseudo-Boolean proof\n")
    end
end
function writerepartition(path,file,cone,nbopb)
    open(string(path,"/repartition"), "a") do f
        write(f,string(file,"\n"))
        for i in eachindex(cone)
            if cone[i] 
                write(f,string("1"))
            else
                write(f,string("."))
            end
            if i==nbopb
                write(f,string("\n"))
            end
        end
        write(f,string("\n"))
    end
end
function writeshortrepartition(path,file,cone,nbopb)
    open(string(path,"/arepartition"), "a") do f
        chunk = nbopb ÷ 100
        proofchunk = (length(cone)-nbopb) ÷ 100
        write(f,string(file," opb and proof chunks are :",chunk," ",proofchunk,"\n"))
        s = 0
        j = 1
        for i in eachindex(cone)
            if cone[i] 
                s += cone[i]
            end
            if i-j==chunk
                if s == 0
                    write(f,string("."))
                else
                    write(f,string(" ",100s÷chunk))
                end
                s = 0 
                j = i
            end
            if i==nbopb
                write(f,string(" ",s,"\n"))
                chunk = proofchunk
                s = 0
                j = i
            end
        end
        write(f,string(" ",s,"\n"))
    end
end
function prettybytes(b)
    if b>=10^9
        return string(round(b/(10^9); sigdigits=4)," GB")
    elseif b>=10^6
        return string(round(b/(10^6); sigdigits=4)," MB")
    elseif b>=10^3
        return string(round(b/(10^3); sigdigits=4)," KB")
    else
        return  string(round(b; sigdigits=4)," B")
    end
end 
function prettytime(b)
    if b<0.01
        return  string(0)
    elseif b<0.1
        return  string(round(b; sigdigits=1))
    elseif b<1
        return  string(round(b; sigdigits=2))
    else
        return  string(round(b; sigdigits=3))
    end
end
function prettypourcent(b)
    b = b*100
    c = round(Int,b)
    return  string(c)
end
function runtrimer(file)
    try
    sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"
    nline = parse(Int,split(read(`wc -l $path/$file$extention`,String)," ")[1])
    if !sat && nline>10
        tri = @elapsed begin
            system,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)
        end
        normcoefsystem(system)
        tms = @elapsed begin
            cone = makesmol(system,invsys,varmap,systemlink,nbopb)
        end
        twc = @elapsed begin
            writeconedel(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
        end
        writeshortrepartition(path,file,cone,nbopb)
        so = stat(string(path,"/",file,".opb")).size + stat(string(path,"/",file,extention)).size
        st = stat(string(path,"/smol.",file,".opb")).size + stat(string(path,"/smol.",file,extention)).size
        color = 1
        if so>st
            color = 2
        end
        printstyled(file,"   trim : ",prettybytes(so),"  ->  ",prettybytes(st),"       ",
            round(tri+tms+twc; sigdigits=4),'=',round(tri; sigdigits=4),"+",
            round(tms; sigdigits=4),"+",round(twc; sigdigits=4)," s\n"; color = color)
        open(string(path,"/attimes"), "a") do f
            write(f,string(file,"/",round(tri; sigdigits=4),"/",
            round(tms; sigdigits=4),"/",round(twc; sigdigits=4),",\n"))
        end
    end
    catch
        println("No ",file," to trim")
    end
end
function runveriPB(file)
    try
    sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"
    nline = parse(Int,split(read(`wc -l $path/$file$extention`,String)," ")[1])
    if !sat && nline>10
        tvp = @elapsed begin
            v1 = read(`veripb $path/$file.opb $path/$file$extention`)
        end
        tvs = @elapsed begin
            v2 = read(`veripb $path/smol.$file.opb $path/smol.$file$extention`)
        end
        so = stat(string(path,"/",file,".opb")).size + stat(string(path,"/",file,extention)).size
        st = stat(string(path,"/smol.",file,".opb")).size + stat(string(path,"/smol.",file,extention)).size
        color = 1
        if tvp>tvs
            color = 2
        end
        printstyled(file,"   trim : ",prettybytes(so),"  ->  ",prettybytes(st),"       ",
            round(tvp; sigdigits=4)," s  ->  ",round(tvs; sigdigits=4)," s\n"; color = color)
        open(string(path,"/abytes"), "a") do f
            write(f,string(file,"/",so/10^6,"/",st/10^6,",\n"))
        end
        open(string(path,"/avtimes"), "a") do f
            write(f,string(file,"/",round(tvp; sigdigits=4),"/",round(tvs; sigdigits=4),",\n"))
        end
        if color == 1
            open(string(path,"/aworst"), "a") do f
                write(f,string(file,"\n")) 
            end
        end
        if v1!=v2
            printstyled("catch (u cant see me)\n"; color = :red)
            open(string(path,"/afailedtrims"), "a") do f
                write(f,string(file," \n"))
            end
        end
    elseif sat
        # println("SAT")
    else
        # println("atomic")
    end
    catch
        println("No ",file," to veri")
    end
end
function roundt(t,d)
    for i in eachindex(t)
        t[i] = round(t[i],digits = d)
    end
    return t
end
function delindividualist(g)
    i = findfirst(v->degree(g,v)==0,vertices(g))
    while !(i === nothing)
        rem_vertex!(g, i)
        i = findfirst(v->degree(g,v)==0,vertices(g))
    end
end
function makeg2win(g)
    n = nv(g)
    g2 = SimpleGraph(n,0)
    for i in vertices(g)
        for j in neighbors(g, i)
            for k in neighbors(g, j)
                add_edge!(g2,i,k)
            end
        end
    end
    return g2
end 
function add_nei(deb,cur,l,g,A)
    if k == 0 A[deb,cur] +=1 
    else
        for nei in neighbors(g, cur)
            add_nei(deb,nei,l-1,g,A)
        end
    end
end
function makegkwin(g,k) return makegkwin(g,2,k) end
function makegkwin(g,l,k) # l length of path (default 2); k number of paths
    n = nv(g)
    A = zeros(Int,n,n)
    gg = [SimpleGraph(n,0) for _ in 1:k]
    for i in vertices(g)
        add_nei(i,i,l,g,A)
    end
    for occ in 1:k
        for i in 1:n
            for j in i:n
                if A[i,j]>=occ
                    add_edge!(gg[occ],i,j)
                end
            end
        end
    end
    return gg
end 
function printcom(file,system,invsys,cone,com)
    names = [
        "backtrack", "backtrackbin", "backtrackbincolor", "disconnected",
        "degre", "hall", "nds", "nogood", "loops", "fail", "colorbound",
        "adjacencyhack", "adjacencydist1", "adjacencydist2", "adjacencydist3",
        "adjacency", "adjacency0", "adjacency1", "adjacency2", "adjacency3", "adjacency4"]
    n = length(names)
    og = zeros(Int,n)
    sm = zeros(Int,n)
    # ogg =  SimpleGraph()
    # smg =  SimpleGraph()
    ogd = Dict{Int,SimpleGraph{Int}}()
    smd = Dict{Int,SimpleGraph{Int}}()
    for i in eachindex(com)
        s = com[i]
        st = split(s,' ')
        type = string(st[1])
        removespaces(st)
        j = findfirst(isequal(type),names)
        if j === nothing
            push!(names,type)
            push!(og,1)
            push!(sm,0)
            if cone[i] sm[end]+=1 end
        else
            og[j]+=1
            if cone[i] sm[j]+=1 end
            if type[1:3] == "adj"
                v1 = parse(Int,st[2])
                v2 = parse(Int,st[3])
                idg = parse(Int,st[4])
                if !haskey(ogd,idg) ogd[idg] = SimpleGraph() end
                if !haskey(smd,idg) smd[idg] = SimpleGraph() end
                ogg = ogd[idg]
                smg = smd[idg]
                n = size(ogg, 1)
                m = max(v1,v2)
                if m > n 
                    add_vertices!(ogg, m-n)
                    add_vertices!(smg, m-n)
                end
                add_edge!(ogg, v1, v2)
                if cone[i] add_edge!(smg, v1, v2) end
            end
        end
    end
    p = sortperm(names)
    for i in p
        if og[i]>0
            col =  sm[i]==og[i] ? 3 : sm[i]==0 ? 1 : 2
            printstyled(names[i]," ",sm[i],"/",og[i],"\n"; color = col)
        end
    end
    for i in eachindex(ogd)
        ogg = ogd[i]
        delindividualist(ogg)
        draw(PNG(string(proofs,"/aimg/",file,"-g",i,".png"), 16cm, 16cm), gplot(ogg))
    end
    for i in eachindex(smd)
        smg = smd[i]
        delindividualist(smg)
        if nv(smg)>1
            draw(PNG(string(proofs,"/aimg/",file,"-g",i,".smol.png"), 16cm, 16cm), gplot(smg))
        end
    end
end
function runtrimmer(file)
    # run_bio_solver(file) # rerun for the pbp file with coms
    tvp = @elapsed begin
        v1 = read(`veripb $proofs/$file.opb $proofs/$file$extention`)
    end
    tri = @elapsed begin
        system,systemlink,redwitness,nbopb,varmap,output,conclusion,com,version = readinstance(proofs,file)
    end
    invsys = getinvsys(system,varmap)
    normcoefsystem(system)
    tms = @elapsed begin
        cone = makesmol(system,invsys,varmap,systemlink,nbopb)
    end
    twc = @elapsed begin
        writeconedel(proofs,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
    end

    printcom(file,system,invsys,cone,com)

    writeshortrepartition(proofs,file,cone,nbopb)
    tvs = @elapsed begin
        v2 = read(`veripb $proofs/smol.$file.opb $proofs/smol.$file$extention`)
    end
    so = stat(string(proofs,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size
    st = stat(string(proofs,"/smol.",file,".opb")).size + stat(string(proofs,"/smol.",file,extention)).size
    t = [roundt([parse(Float64,file[end-5:end-3]),parse(Float64,file[end-2:end]),so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    printtabular(t)
    open(string(proofs,"/atable"), "a") do f
        write(f,string(t[1],",\n"))
    end
    if v1!=v2
        printstyled("catch (u cant see me)\n"; color = :red)
        open(string(proofs,"/afailedtrims"), "a") do f
            write(f,string(file," \n"))
        end
    end
end
function run_bio_sorted()
    # extentionstat = ".veripb"
    cd()
    list = cd(readdir, proofs)
    list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:3]=="bio"]
    stats = [stat(string(path,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size for file in list]
    p = sortperm(stats)
    for i in eachindex(p)
        file = list[p[i]]
        tail = read(`tail -n 1 $proofs/$file$extention`,String)
        if length(tail) > 24 && 
            tail[1:24] == "end pseudo-Boolean proof" &&
            read(`tail -n 2 $proofs/$file$extention`,String)[1:14] != "conclusion SAT"
            if stats[p[i]] > 2_000_000
                runtrimmer(file)
            end
        end
    end
end
function run_timeout_bio_solver()
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    n = length(graphs)
    for target in graphs, pattern in graphs
        # target = graphs[rand(1:n)]
        # pattern = graphs[rand(1:n)]
        if pattern != target
            ins = string("bio",pattern[1:end-4],target[1:end-4])
            if !isfile(string(proofs,"/",ins,".opb")) || !isfile(string(proofs,"/",ins,extention)) ||
                (isfile(string(proofs,"/",ins,extention)) && 
                (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                print(ins)
                p = run(pipeline(`timeout 3 ./$solver --prove $proofs/$ins --no-clique-detection --format lad $path/$pattern $path/$target`, devnull),wait=false); wait(p)
            end # no --proof-names anymore ?
        end
    end
end
function run_bio_list(l=1,u=length(biolist),m=1)
    p = sortperm(biostats)
    for i in l:m:u
        print(i," ")
        # println(biostats[p[i]])
        runtrimmer(biolist[p[i]])
    end
end
function run_bio_solver(ins)
    path = string(benchs,"/biochemicalReactions")
    cd()
    pattern = string(ins[4:6],".txt")
    target = string(ins[7:9],".txt")

    g = ladtograph(path,pattern)
    draw(PNG(string(proofs,"/aimg/",pattern[1:3],".png"), 16cm, 16cm), gplot(g))
    draw(PNG(string(proofs,"/aimg/",pattern[1:3],"-g2.png"), 16cm, 16cm), gplot(makeg2win(g)))
    g = ladtograph(path,target)
    draw(PNG(string(proofs,"/aimg/",target[1:3],".png"), 16cm, 16cm), gplot(g))
    draw(PNG(string(proofs,"/aimg/",target[1:3],"-g2.png"), 16cm, 16cm), gplot(makeg2win(g)))


    # run(`rm $proofs/$ins$extention`)
    # ins = string("bio",pattern[1:end-4],target[1:end-4])
    # if !isfile(string(proofs,"/",ins,".opb")) || !isfile(string(proofs,"/",ins,extention)) ||
    #     (isfile(string(proofs,"/",ins,extention)) && 
    #     (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
    #     read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
        print(ins)
        # @time run(pipeline(`./$solver --no-clique-detection --format  lad $path/$pattern $path/$target`, devnull))
        @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --format  lad $path/$pattern $path/$target`, devnull))
        # @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --no-supplementals --format  lad $path/$pattern $path/$target`, devnull))
        # @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --no-nds --no-supplementals --format  lad $path/$pattern $path/$target`, devnull))
    # end # no --proof-names anymore ?
end
function okinstancelist()
    cd()
    list = cd(readdir, proofs)
    list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:3]=="bio"]
    list = [s for s in list if isfile(string(proofs,"/",s,extention))]
    list = [s for s in list if read(`tail -n 1 $proofs/$s$extention`,String) == "end pseudo-Boolean proof\n"]
    list = [s for s in list if read(`tail -n 2 $proofs/$s$extention`,String)[1:14] != "conclusion SAT"]
    stats = [stat(string(path,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size for file in list]

    for i in eachindex(list)
        s = list[i]
        if read(`tail -n 1 $proofs/$s$extention`,String) != "end pseudo-Boolean proof\n"
            # println(s," ",stats[i])
            # println(read(`tail -n 1 $proofs/$s$extention`,String))
        end
    end
    # p = sortperm(stats)
    # listm = [list[i] for i in eachindex(list) if stats[i] > 1_000_000]
    open(string(proofs,"/abiolist.jl"),"w") do f
        write(f,string("const biolist = [\"",list[1],"\""))
        for i in 2:length(list) 
            write(f,string(",\"",list[i],"\""))
        end
        write(f,string("]\n"))
        write(f,string("const biostats = [",stats[1]))
        for i in 2:length(list) 
            write(f,string(",",stats[i]))
        end
        write(f,string("]\n"))
    end
end
const benchs = "veriPB/newSIPbenchmarks"
const solver = "veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
const proofs = "veriPB/proofs"    
# const proofs = "veriPB/prooframdisk"    
# const benchs = "newSIPbenchmarks"
# const solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
# const proofs = "/cluster/proofs"
# const extention = ".veripb"
const extention = ".pbp"
# const path = proofs
const version = "2.0"

cd()
# include(string("abiolist.jl"))
include("ladtograph.jl")

function readrepartition()
    nb = 0
    cko = 0
    ckp = 0
    Σ = [0 for i in 1:101]
    cd()
    c = 1
    open(string(proofs,'/',"servarepartition"),"r"; lock = false) do f
        for ss in eachline(f)
            c+=1
            if ss!="" && ss[1] == 'b'
                st  = split(ss,' ')
                cko = parse(Int,st[end-1][2:end])
                ckp = parse(Int,st[end])
                c   = 1
            elseif ckp>1 && ckp<100 && c==3
                nb += 1
                st = split(ss,' ')
                i = 1
                for s in st
                    nbp = count('.',s)
                    if nbp>0
                        s = replace(s,'.'=>"")
                    end
                    if s!="" && i<102
                        Σ[i] += parse(Int,s)
                        i+=1
                    end
                    i+=nbp
                end
            end
        end
    end
    println(nb)
    t = Σ./nb
    for i in eachindex(t)
        print(string(i,'/',round(t[i]; sigdigits=4),','))
    end
    # return Σ./nb
end
function printtabular(t)
    for i in t 
        println(
        round(Int,i[1])," & ",
        round(Int,i[2])," & ",
        prettybytes(i[3])," & ",
        prettybytes(i[4])," & ",
        prettypourcent(i[5])," & ",
        prettytime(i[6])," & ",
        prettytime(i[7])," & ",
        prettypourcent(i[8])," & ",
        prettytime(i[9])," & ",
        prettytime(i[10])," & ",
        prettytime(i[11])," \\\\\\hline"
        )
    end
end
function main()
    run_bio_list(13226,length(biolist),1)
end

# main()

function generate_biographs(k = 4)
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    for f in graphs
        print(f)
        g = ladtograph(path,f)
        delindividualist(g)
        draw(PNG(string(proofs,"/aimg/",f[1:3],".png"), 16cm, 16cm), gplot(g))
        gg = makegkwin(g,k)
        for i in 1:k
            g = gg[i]
            delindividualist(g)
            if nv(g)>1
            draw(PNG(string(proofs,"/aimg/",f[1:3],"-g",i,".png"), 16cm, 16cm), gplot(g))
        end end
    end
end
# generate_biographs()

# ins = "bio666777"
# runtrimmer(ins)

# pattern  = "666.csv"
# target = "777.csv"

# ins  = "whe666777"
# file = ins
# cd()
# path = "veriPB/trim/smol-proofs2"

# g = csvtograph(path,pattern)
# draw(PNG(string(proofs,"/aimg/",pattern[1:3],".png"), 16cm, 16cm), gplot(g))
# draw(PNG(string(proofs,"/aimg/",pattern[1:3],"-g2.png"), 16cm, 16cm), gplot(makeg2win(g)))
# g = csvtograph(path,target)
# draw(PNG(string(proofs,"/aimg/",target[1:3],".png"), 16cm, 16cm), gplot(g))
# draw(PNG(string(proofs,"/aimg/",target[1:3],"-g2.png"), 16cm, 16cm), gplot(makeg2win(g)))

# @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --format csv $path/$pattern $path/$target`, devnull))
# runtrimmer(ins)
# @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --no-nds --format csv $path/$pattern $path/$target`, devnull))
# runtrimmer(ins)
# @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --no-supplementals --format csv $path/$pattern $path/$target`, devnull))
# runtrimmer(ins)
# @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --no-nds --no-supplementals --format csv $path/$pattern $path/$target`, devnull))
# runtrimmer(ins)



#=
 no-suplementals

graphs from 13000 to 14851
14852 bio046070  0.417385 seconds (109 allocations: 6.234 KiB)


gpath 2,k 

au moins k chemins de taille
=#


# run_timeout_bio_solver()
# run_bio_sorted()


# ins = "aaaclique"
# cd()
# ins = "bio021002"
# runtrimmer(proofs,ins,extention)

ins = "bio037002"
# ins = "bio019014"
# ins = "bio112002"

# long "bio055018"


# ins = "bio021002"
# ins = "bio070014"

# run_bio_solver(ins)

runtrimmer(ins)


# sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"


# main()

#=
export JULIA_NUM_THREADS=192
julia --check-bounds=no 'trimer 5.jl'

degre
nds
hall
fail
backtrack
adjacency0:n
adjacencyhack
backtrackbincolor
backtrackbin
colorbound
disconnected

rm atimes
rm abytes
rm afailedtrims
rm aworst
rm arepartition

hardest one bio 7 13 (310_916_484 lignes)
lon sur le serv bio 89 32 (421_805_749 lignes)

on peut retenir l'assignement optenable depuis le cone
on met dans le cone toutes les unit


=#

# readrepartition()

# scp -r \\wsl.localhost\Ubuntu\home\arthur_gla\veriPB\trim\smol-proofs2\Instances\ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/smol-proofs2
# scp -r /home/arthur_gla/veriPB/newSIPbenchmarks/ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/
# find . -name "*Zone.Identifier" -type f -delete 
# find . -name ".*" -type f -delete 
# ssh arthur@fataepyc-01.dcs.gla.ac.uk
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/smol.bio063002.veripb smol.bio063002.veripb
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/smol.bio170041.veripb smol.bio170041.veripb
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/times times2
# cd /home/arthur_gla/veriPB/trim/smol-proofs2/
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/atable atableserv
#=
function test()
    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][6]),",")
    end
    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][7]),",")
    end

    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][9]),",")
    end
    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][10]),",")
    end
    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][11]),",")
    end

    r =  9500:length(t)
    s = 0.0
    for i in r
        s+=t[i][8]
    end
    println(s/length(r))

    r =  9500:length(t)
    m = 0.0
    for i in r
        m=max(m,t[i][5])
    end
    println(m)

    r =  9500:length(t)
    m = 100.0
    for i in r
        m=min(m,t[i][5])
    end
    println(m)

    r =  9500:length(t)
    t5 = [t[i][5] for i in r]
    t8 = [t[i][8] for i in r]

    for i in r
        if t[i][8]>0.8
            printtabular([t[i]])
        end
    end

    for i in 9000:length(t)
        print(prettytime(t[i][3]/10^6),"/",prettypourcent(t[i][8]),",")
    end

    for i in 9000:length(t)
        print(prettytime(t[i][3]/10^6),"/",prettytime(t[i][4]/10^6),",")
    end

    for i in 9000:length(t)
        print(prettytime(t[i][3]/10^6),"/",prettytime(t[i][4]/10^6),",")
    end
end
=#