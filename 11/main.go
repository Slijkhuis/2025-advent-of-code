package main

import (
	"fmt"
	"os"
	"strings"

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
	for line := range aoc.LinesFromFile(os.Args[2]) {
		fmt.Println(line)
	}
}
