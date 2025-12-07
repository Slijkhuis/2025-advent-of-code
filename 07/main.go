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
	g := aoc.BuildGridFromFile(os.Args[2])
	startPoint := g.MustFindFirstPointWithValue('S')
	splits := make(map[aoc.Point]bool)

	var moveDown func(c aoc.Point)

	moveDown = func(p1 aoc.Point) {
		p2 := p1.Move(aoc.Down)
		r, ok := g.Data[p2]
		if !ok {
			return
		}

		if r == '^' {
			_, ok := splits[p2]
			if ok {
				return
			}

			splits[p2] = true
			moveDown(p2.Move(aoc.Left))
			moveDown(p2.Move(aoc.Right))
		} else {
			moveDown(p2)
		}
	}

	moveDown(startPoint)

	fmt.Println(len(splits))
}

func part2() {
	g := aoc.BuildGridFromFile(os.Args[2])
	startPoint := g.MustFindFirstPointWithValue('S')
	timelines := map[aoc.Point]int{}
	timelines[startPoint] = 1
	for y := 0; y < g.Height; y++ {
		for x := 0; x < g.Width; x++ {
			p := aoc.Point{X: x, Y: y}
			v, ok := g.Data[p]
			if !ok {
				continue
			}
			switch v {
			case 'S', '.':
				pDown := p.Move(aoc.Down)
				timelines[pDown] += timelines[p]
			case '^':
				pLeft := p.Move(aoc.Left).Move(aoc.Down)
				pRight := p.Move(aoc.Right).Move(aoc.Down)
				timelines[pLeft] += timelines[p]
				timelines[pRight] += timelines[p]
			}
		}
	}

	numberOfTimelines := 0
	for x := 0; x < g.Width; x++ {
		numberOfTimelines += timelines[aoc.Point{X: x, Y: g.Height - 1}]
	}

	fmt.Println(numberOfTimelines)
}
