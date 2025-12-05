package main

import (
	"fmt"
	"os"
	"sort"
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
	rangesStr := strings.Split(sections[0], "\n")

	var ranges [][2]int
	for _, r := range rangesStr {
		parts := strings.Split(r, "-")
		ranges = append(ranges, [2]int{aoc.Atoi(parts[0]), aoc.Atoi(parts[1])})
	}

	availableIngredients := strings.Split(sections[1], "\n")
	freshIngredients := 0

	for _, ingredient := range availableIngredients {
		if ingredient == "" {
			continue
		}

		ingredientID := aoc.Atoi(ingredient)
		spoiled := true

		for _, r := range ranges {
			if ingredientID >= r[0] && ingredientID <= r[1] {
				spoiled = false
				break
			}
		}

		if !spoiled {
			freshIngredients++
		}
	}

	aoc.Println(t, freshIngredients)
}

func part2() {
	t := time.Now()
	sections := aoc.SectionsFromFileAsString(os.Args[2])
	rangesStr := strings.Split(sections[0], "\n")

	var ranges Ranges
	for _, r := range rangesStr {
		parts := strings.Split(r, "-")
		ranges = append(ranges, Range{start: aoc.Atoi(parts[0]), end: aoc.Atoi(parts[1])})
	}

	sort.Sort(ranges)
	mergedRanges := mergeRanges(ranges)

	total := 0
	for _, r := range mergedRanges {
		total += r.end - r.start + 1
	}

	aoc.Println(t, total)
}

type Range struct {
	start int
	end   int
}

type Ranges []Range

func (r Ranges) Len() int {
	return len(r)
}
func (r Ranges) Less(i, j int) bool {
	return r[i].start < r[j].start
}

func (r Ranges) Swap(i, j int) {
	r[i], r[j] = r[j], r[i]
}

func mergeRanges(ranges Ranges) Ranges {
	var merged Ranges
	for _, r := range ranges {
		if len(merged) == 0 || merged[len(merged)-1].end < r.start-1 {
			merged = append(merged, Range{start: r.start, end: r.end})
		} else {
			if merged[len(merged)-1].end < r.end {
				merged[len(merged)-1].end = r.end
			}
		}
	}
	return merged
}
