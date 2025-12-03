package main

import (
	"fmt"
	"os"
	"sort"
	"strconv"
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
	joltages := []int{}
	for line := range aoc.LinesFromFile(os.Args[2]) {
		batteries := aoc.Map(strings.Split(line, ""), func(s string) int {
			i, err := strconv.Atoi(s)
			aoc.Fail(err)
			return i
		})

		first := 0
		lastSetPosition := 0
		second := 0

		for i := 0; i < len(batteries)-1; i++ {
			if first < batteries[i] {
				first = batteries[i]
				lastSetPosition = i
			}
		}

		for i := lastSetPosition + 1; i < len(batteries); i++ {
			if second < batteries[i] {
				second = batteries[i]
			}
		}

		joltage, _ := strconv.Atoi(fmt.Sprintf("%d%d", first, second))
		aoc.Debug(joltage)
		joltages = append(joltages, joltage)
	}

	fmt.Println(aoc.Sum(joltages))
}

func part2() {
	joltages := []int{}
	for line := range aoc.LinesFromFile(os.Args[2]) {
		var batteries []Battery

		for i := 0; i < len(line); i++ {
			value, err := strconv.Atoi(string(line[i]))
			aoc.Fail(err)
			battery := Battery{
				Index: i,
				Value: value,
			}
			batteries = append(batteries, battery)
		}

		sort.Slice(batteries, func(i, j int) bool {
			if batteries[i].Value == batteries[j].Value {
				return batteries[i].Index < batteries[j].Index
			}
			return batteries[i].Value > batteries[j].Value
		})

		var joltageStr string

		for i := 0; i < 12; i++ {
			battery := findHighestBelowIndex(batteries, len(line)-12+i+1)
			joltageStr += strconv.Itoa(battery.Value)
			batteries = removeBelowIndex(batteries, battery.Index)
		}

		joltage, _ := strconv.Atoi(joltageStr)
		aoc.Debug(joltage)
		joltages = append(joltages, joltage)
	}

	fmt.Println(aoc.Sum(joltages))
}

type Battery struct {
	Index int
	Value int
}

func findHighestBelowIndex(batteries []Battery, index int) Battery {
	for _, battery := range batteries {
		if battery.Index < index {
			return battery
		}
	}

	return Battery{}
}

func removeBelowIndex(batteries []Battery, index int) []Battery {
	var result []Battery
	for _, b := range batteries {
		if b.Index > index {
			result = append(result, b)
		}
	}

	return result
}
