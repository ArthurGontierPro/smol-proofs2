function plotresultstablenature(file)
    table = Vector{Vector{Any}}()
    legende = Vector{String}()
    n = 0
    file = string(pwd(),'/',file)
    println(file)
    open(file, "r") do f
        firstline = readline(f)
        legende = split(firstline,' ')
        n = length(legende)
        for line in eachline(f)
            st = split(line,' ')
            t = Vector{Any}()
            for i in 1:n
                push!(t,tryparse(Float64,st[i]))
            end
            push!(table,t)
        end
    end
    # veripb elaborate vs trimming elaborate
    # printpoints2Dlog(table,2,8)
    # veri vs trim
    printpoints2Dlog(table,5,11)
end
function printpoints2D(table,a,b)
    for t in table 
        if t[a]!==nothing &&t[b]!==nothing
            print(t[a],'/',t[b],',')
        end
    end
    println()
end
function printpoints2Dlog(table,a,b)
    for t in table 
        if t[a]!==nothing &&t[b]!==nothing
            print(
                logsmooth(t[a]),'/',
                logsmooth(t[b]),',')
        end
    end
    println()
end
function logsmooth(a)
    return round(max(log10(a),0),digits = 3)
end
plotresultstablenature(ARGS[1])