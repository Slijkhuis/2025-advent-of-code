package main

import (
	"fmt"
	"math"
	"os"
	"sort"

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

type Point struct {
	X, Y, Z int
}

func (p Point) DistanceTo(other Point) float64 {
	dx := float64(p.X - other.X)
	dy := float64(p.Y - other.Y)
	dz := float64(p.Z - other.Z)
	return math.Sqrt(dx*dx + dy*dy + dz*dz)
}

type Distance struct {
	From     Point
	To       Point
	Distance float64
}

type Circuit struct {
	Members map[Point]struct{}
}

func part1() {
	var junctions []Point

	for line := range aoc.LinesFromFile(os.Args[2]) {
		ints := aoc.IntsFromString(line)
		p := Point{X: ints[0], Y: ints[1], Z: ints[2]}
		junctions = append(junctions, p)
	}

	processsedDistances := map[[2]Point]struct{}{}

	var distances []Distance
	for _, p1 := range junctions {
		for _, p2 := range junctions {
			if p1 == p2 {
				continue
			}

			pair := [2]Point{p2, p1}
			if _, ok := processsedDistances[pair]; ok {
				continue
			}
			processsedDistances[[2]Point{p1, p2}] = struct{}{}

			distances = append(distances, Distance{
				From:     p1,
				To:       p2,
				Distance: p1.DistanceTo(p2),
			})
		}
	}

	sort.Slice(distances, func(i, j int) bool {
		return distances[i].Distance < distances[j].Distance
	})

	var circuits []*Circuit
	circuitMembership := map[Point]*Circuit{}

	numberOfConnections := 0
	maxNumberOfConnections := 1000
	if aoc.DebugMode {
		maxNumberOfConnections = 10
	}

	for _, dist := range distances {
		c1, ok1 := circuitMembership[dist.From]
		c2, ok2 := circuitMembership[dist.To]

		aoc.Debug(dist.From, dist.To, dist.Distance)

		if ok1 && ok2 {
			if c1 == c2 {
				// already in the same circuit
				aoc.Debug("skipping (already same circuit)\n---")
				numberOfConnections++ // why is this necessary?
				continue
			} else {
				// merge circuits
				for member := range c2.Members {
					c1.Members[member] = struct{}{}
					circuitMembership[member] = c1
					c2.Members = nil
				}
			}
		} else if ok1 {
			c1.Members[dist.To] = struct{}{}
			circuitMembership[dist.To] = c1
		} else if ok2 {
			c2.Members[dist.From] = struct{}{}
			circuitMembership[dist.From] = c2
		} else {
			newCircuit := &Circuit{Members: map[Point]struct{}{
				dist.From: {},
				dist.To:   {},
			}}
			circuits = append(circuits, newCircuit)
			circuitMembership[dist.From] = newCircuit
			circuitMembership[dist.To] = newCircuit
		}

		numberOfConnections++
		if numberOfConnections >= maxNumberOfConnections {
			break
		}
	}

	sort.Slice(circuits, func(i, j int) bool {
		return len(circuits[i].Members) > len(circuits[j].Members)
	})

	fmt.Println(aoc.Product([]int{
		len(circuits[0].Members),
		len(circuits[1].Members),
		len(circuits[2].Members),
	}))
}

func part2() {
	for line := range aoc.LinesFromFile(os.Args[2]) {
		fmt.Println(line)
	}
}
