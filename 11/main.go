package main

import (
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/Slijkhuis/2025-advent-of-code/pkg/aoc"
)

func main() {
	if len(os.Args) != 3 {
		fmt.Println("Usage: go run main.go <part> <input-file>")
		os.Exit(1)
	}

	switch os.Args[1] {
	case "1":
		part1()
	case "2":
		part2()
	default:
		fmt.Println("Invalid part")
		os.Exit(1)
	}
}

func part1() {
	g := aoc.NewGraph[string, int]()

	for line := range aoc.LinesFromFile(os.Args[2]) {
		s := strings.Split(line, ": ")
		from := g.NewOrExistingNode(s[0], 0)
		toKeys := strings.Split(s[1], " ")
		for _, toKey := range toKeys {
			to := g.NewOrExistingNode(toKey, 0)
			g.AddEdge(from, to)
		}
	}

	you := g.Nodes["you"]
	out := g.Nodes["out"]

	paths := g.FindAllPaths(you, out)
	fmt.Printf("Number of paths from 'you' to 'out':\n%d\n", len(paths))
}

func part2() {
	t := time.Now()
	g := aoc.NewGraph[string, int]()

	for line := range aoc.LinesFromFile(os.Args[2]) {
		s := strings.Split(line, ": ")
		from := g.NewOrExistingNode(s[0], 0)
		toKeys := strings.Split(s[1], " ")
		for _, toKey := range toKeys {
			to := g.NewOrExistingNode(toKey, 0)
			g.AddEdge(from, to)
		}
	}

	aoc.Println(t, "parsed graph, number of nodes:", len(g.Nodes))

	svr := g.Nodes["svr"]
	fft := g.Nodes["fft"]
	dac := g.Nodes["dac"]
	out := g.Nodes["out"]

	dacToFFT := g.PathExists(dac, fft)
	if dacToFFT {
		panic("there's a path from dac to fft")
	}
	// svr -> fft -> dac -> out
	aoc.Println(t, "asserted no path from dac to fft")

	// Massive assumption: it's a DAG? -> yes it is!

	c1 := g.CountPathsInDAG(svr, fft)
	aoc.Println(t, "svr->fft", c1)
	c2 := g.CountPathsInDAG(fft, dac)
	aoc.Println(t, "fft->dac", c2)
	c3 := g.CountPathsInDAG(dac, out)
	aoc.Println(t, "dac->out", c3)

	totalPaths := c1 * c2 * c3
	aoc.Println(t, totalPaths)
}
