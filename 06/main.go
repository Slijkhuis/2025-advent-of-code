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
	var numbers [][]int
	var operations []string

	for line := range aoc.LinesFromFile(os.Args[2]) {
		if line[0] == '+' || line[0] == '*' {
			operations = strings.Fields(line)
			continue
		}
		numbers = append(numbers, aoc.IntsFromString(line))
	}

	var result int

	for i, ops := range operations {
		nums := aoc.Map(numbers, func(s []int) int {
			return s[i]
		})

		switch ops[0] {
		case '+':
			result += aoc.Sum(nums)
		case '*':
			result += aoc.Product(nums)
		default:
			panic("unknown operation")
		}
	}

	fmt.Println(result)
}

func part2() {
	g := aoc.BuildGridFromFile(os.Args[2])

	var result int
	var numbers [][]int
	var operations []string
	var currentNumbers []int

	for x := g.Width - 1; x >= 0; x-- {
		numberStr := ""
		for y := 0; y < g.Height-1; y++ {
			v := g.Data[aoc.Point{X: x, Y: y}]
			if v != ' ' {
				numberStr += string(v)
			}
		}

		if numberStr == "" {
			continue
		}

		currentNumbers = append(currentNumbers, aoc.Atoi(numberStr))

		opVal := g.Data[aoc.Point{X: x, Y: g.Height - 1}]
		if opVal == ' ' {
			continue
		}

		operations = append(operations, string(opVal))
		numbers = append(numbers, currentNumbers)
		currentNumbers = []int{}
	}

	for i, ops := range operations {
		switch ops[0] {
		case '+':
			result += aoc.Sum(numbers[i])
		case '*':
			result += aoc.Product(numbers[i])
		default:
			panic("unknown operation")
		}
	}

	fmt.Println(result)
}
