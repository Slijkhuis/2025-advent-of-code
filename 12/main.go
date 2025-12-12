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
	t := time.Now()
	sections := aoc.SectionsFromFileAsString(os.Args[2])
	shapeMap := make(map[int]int)

	for i, s := range sections[:len(sections)-1] {
		area := 0
		for _, r := range s {
			if r == '#' {
				area++
			}
		}
		shapeMap[i] = area
	}
	aoc.Println(t, "parsed shapes")

	ans := 0
	for _, line := range strings.Split(strings.TrimSpace(sections[len(sections)-1]), "\n") {
		parts := strings.Split(line, ": ")

		totalArea := 0
		totalCount := 0
		for index, count := range aoc.IntsFromString(parts[1]) {
			for i := 0; i < count; i++ {
				totalArea += shapeMap[index]
				totalCount++
			}
		}

		sizeParts := aoc.IntsFromString(parts[0])

		gridArea := sizeParts[0] * sizeParts[1]
		if totalArea > gridArea {
			aoc.Debug("skipping because shape area exceeds grid area:", line)
			continue
		}

		if totalCount*9 <= gridArea {
			ans++
			continue
		}

		// Here a very difficult packing algorithm would be implemented, but it seems it's not necessary?
		panic("do we get here?")
	}

	aoc.Println(t, ans)
}

func part2() {
	fmt.Println("Thanks for the amazing puzzles!")
}
