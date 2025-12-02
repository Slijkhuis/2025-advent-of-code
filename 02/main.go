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
	ranges := strings.Split(aoc.StringFromFile(os.Args[2]), ",")
	var invalidProductIDs []int
	for _, r := range ranges {
		bounds := strings.Split(r, "-")
		from := aoc.Atoi(strings.TrimSpace(bounds[0]))
		to := aoc.Atoi(strings.TrimSpace(bounds[1]))
		for i := from; i <= to; i++ {
			if isANumberThatIsRepeatingTwice(fmt.Sprintf("%d", i)) {
				aoc.Debug(i)
				invalidProductIDs = append(invalidProductIDs, i)
			}
		}
	}

	fmt.Println(aoc.Sum(invalidProductIDs))
}

func part2() {
	ranges := strings.Split(aoc.StringFromFile(os.Args[2]), ",")
	var invalidProductIDs []int
	for _, r := range ranges {
		bounds := strings.Split(r, "-")
		from := aoc.Atoi(strings.TrimSpace(bounds[0]))
		to := aoc.Atoi(strings.TrimSpace(bounds[1]))
		for i := from; i <= to; i++ {
			if findRepeatingKnuthMorrisPratt(fmt.Sprintf("%d", i)) != "" {
				aoc.Debug(i)
				invalidProductIDs = append(invalidProductIDs, i)
			}
		}
	}

	fmt.Println(aoc.Sum(invalidProductIDs))
}

func isANumberThatIsRepeatingTwice(s string) bool {
	n := len(s)
	if n%2 != 0 {
		return false
	}
	half := n / 2
	return s[:half] == s[half:]
}

func findRepeatingKnuthMorrisPratt(s string) string {
	n := len(s)
	lps := make([]int, n)
	length := 0
	i := 1

	for i < n {
		if s[i] == s[length] {
			length++
			lps[i] = length
			i++
		} else {
			if length != 0 {
				length = lps[length-1]
			} else {
				lps[i] = 0
				i++
			}
		}
	}

	repeatingLength := lps[n-1]

	if repeatingLength > 0 && n%(n-repeatingLength) == 0 {
		return s[:n-repeatingLength]
	}

	return ""
}
