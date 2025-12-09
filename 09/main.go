package main

import (
	"fmt"
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

type Area struct {
	From aoc.Point
	To   aoc.Point
	Area int
}

func part1() {
	var redTiles []aoc.Point
	var areas []Area
	for line := range aoc.LinesFromFile(os.Args[2]) {
		ints := aoc.IntsFromString(line)
		redTile := aoc.Point{X: ints[0], Y: ints[1]}
		for _, otherTile := range redTiles {
			areas = append(areas, Area{
				From: redTile,
				To:   otherTile,
				Area: (aoc.Abs(redTile.X-otherTile.X) + 1) * (aoc.Abs(redTile.Y-otherTile.Y) + 1),
			})
		}
		redTiles = append(redTiles, redTile)
	}

	sort.Slice(areas, func(i, j int) bool {
		return areas[i].Area > areas[j].Area
	})

	aoc.Debug(areas[0])
	fmt.Println(areas[0].Area)
}

func part2() {
	for line := range aoc.LinesFromFile(os.Args[2]) {
		fmt.Println(line)
	}
}
