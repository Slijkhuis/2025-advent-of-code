package main

import (
	"fmt"
	"os"

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
	grid := aoc.BuildGridFromFile(os.Args[2])

	accessibleRollsOfPaper := 0

	for cell := range grid.Iter() {
		if cell.Value == '@' {
			adjacentRollsOfPaper := 0
			for _, dir := range aoc.Directions {
				r := grid.AdjOrNull(cell.Point, dir)
				if r == '@' {
					adjacentRollsOfPaper++
				}
			}
			if adjacentRollsOfPaper < 4 {
				accessibleRollsOfPaper++
			}
		}
	}

	fmt.Println(accessibleRollsOfPaper)
}

func part2() {
	grid := aoc.BuildGridFromFile(os.Args[2])

	accessibleRollsOfPaper := 0

	for {
		accessibleRollsOfPaperTmp := 0
		for cell := range grid.Iter() {
			if cell.Value == '@' {
				adjacentRollsOfPaper := 0
				for _, dir := range aoc.Directions {
					r := grid.AdjOrNull(cell.Point, dir)
					if r == '@' {
						adjacentRollsOfPaper++
					}
				}
				if adjacentRollsOfPaper < 4 {
					accessibleRollsOfPaperTmp++
					cell.Value = '.'
					grid.Data[cell.Point] = '.'
				}
			}
		}

		accessibleRollsOfPaper += accessibleRollsOfPaperTmp
		if accessibleRollsOfPaperTmp == 0 {
			break
		}
	}

	fmt.Println(accessibleRollsOfPaper)
}
