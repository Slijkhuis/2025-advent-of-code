package main

import (
	"fmt"
	"os"
	"strconv"
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
	position := 50
	atZero := 0

	for line := range aoc.LinesFromFile(os.Args[2]) {
		sign := 1
		if line[0] == 'L' {
			sign = -1
		}

		i, err := strconv.Atoi(line[1:])
		aoc.Fail(err)

		position += sign * i
		position %= 100

		if position == 0 {
			atZero++
		} else if position < 0 {
			position += 100
		}

		aoc.Debug(position)
	}

	aoc.Println(t, "Times at zero:", atZero)
}

func part2() {
	t := time.Now()
	position := 50
	passedZero := 0

	for line := range aoc.LinesFromFile(os.Args[2]) {
		sign := 1
		if line[0] == 'L' {
			sign = -1
		}

		i, err := strconv.Atoi(line[1:])
		aoc.Fail(err)

		if position == 0 && sign == -1 {
			passedZero--
		}

		position += sign * i

		for position >= 100 {
			passedZero++
			position -= 100
		}

		for position < 0 {
			passedZero++
			position += 100
		}

		if position == 0 && sign == -1 {
			passedZero++
		}

		aoc.Debug(line, position, passedZero)
	}

	aoc.Println(t, "Times at zero:", passedZero)
}
