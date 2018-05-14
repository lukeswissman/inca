# INCA

A tool to navigate answer-set programs using facets. 

## Prerequisites

```
Python (tested with python 2.7)
Clingo (tested with clingo 5.2)
```

Information about Clingo and how to download it is available [here](https://potassco.org/clingo/).
Releases of python are available [here](https://www.python.org/downloads/).

## Running

In order to run INCA, clingo.(pyd / so) needs to be in the same directory of inca.py.
The tool can be launched using the command

```
python inca.py -f <asp_program.lp>
```

## Commands

List of the tool's commands

```
Apply a nav. step using an inclusive facet                    ex: p(y1,y2)
                                               
Apply a nav. step using an exclusive facet                    ex: #not p(y1,y2)
                                          
Retract a specific facet                                      ex: #del p(y1,y2)
                                          
Show the consequences of removing certain facets              ex: #what p(y1,y2)
                                         
Calculate all minimal correction sets w.r.t. some facet       ex: #how p(y1,y2)
                                          
Retract all facets                                            delall
                                                     
List all applied facets                                       lk
                                                         
Display active / inactive facets                              show
                                                       
Terminate the program                                         exit
                                                      
*Note* Multiple entries and deletions must be separated by "/"  

```
## Navigation Example

