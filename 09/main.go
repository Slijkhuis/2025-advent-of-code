package main

import (
	"fmt"
	"os"
	"sort"
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
	t := time.Now()

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

	/*
		While plotting the points in a visualisation tool, I saw that it's basically a circle with a cutout of 2 long
		horizontal lines that the rectangle shouldn't cross.

		My hacky approach is to:
		- first get all areas, order them by size, like in part 1
		- then skip any areas that cross the cutout
		- then skip any areas that have their corners outside the polygon, this should work because the polygon is sort of
		  a circle
	*/

	ys := []int{}
	for i, tile := range redTiles {
		j := (i + 1) % len(redTiles)
		nextTile := redTiles[j]
		lineLength := aoc.Abs(tile.X - nextTile.X)

		if lineLength > 5000 {
			aoc.Println(t, tile, nextTile, lineLength)
			if tile.Y != nextTile.Y {
				panic("long vertical line?")
			}
			ys = append(ys, tile.Y)
		}
	}
	if len(ys) != 2 {
		panic("more or fewer than 2 long lines?")
	}

	skippedBecauseOfCrossing := 0
	skippedBecauseOfOutside := 0
	minY := aoc.Min(ys[0], ys[1])
	maxY := aoc.Max(ys[0], ys[1])
	for i := range areas {
		a := areas[i]
		y1 := aoc.Min(a.From.Y, a.To.Y)
		y2 := aoc.Max(a.From.Y, a.To.Y)

		if y1 <= minY && y2 >= maxY {
			skippedBecauseOfCrossing++
			continue
		}

		corners := getCorners(a)
		areaIsContainedInPolygon := true
		for _, corner := range corners {
			if !isPointInPolygon(redTiles, corner) {
				areaIsContainedInPolygon = false
				break
			}
		}

		if !areaIsContainedInPolygon {
			skippedBecauseOfOutside++
			continue
		}

		aoc.Println(t, "skipped", skippedBecauseOfCrossing, "areas for crossing")
		aoc.Println(t, "skipped", skippedBecauseOfOutside, "areas for outside")
		aoc.Println(t, "found", a)
		aoc.Println(t, a.Area)
		break
	}
}

func getCorners(a Area) []aoc.Point {
	return []aoc.Point{
		{X: a.From.X, Y: a.From.Y},
		{X: a.From.X, Y: a.To.Y},
		{X: a.To.X, Y: a.From.Y},
		{X: a.To.X, Y: a.To.Y},
	}
}

func isPointInPolygon(polygon []aoc.Point, testPoint aoc.Point) bool {
	n := len(polygon)
	if n < 3 {
		return false
	}
	crossings := 0

	for i := 0; i < n; i++ {
		j := (i + 1) % n
		p1 := polygon[i]
		p2 := polygon[j]

		if p1.Y == p2.Y && p1.Y == testPoint.Y {
			minX := min(p1.X, p2.X)
			maxX := max(p1.X, p2.X)
			if testPoint.X >= minX && testPoint.X <= maxX {
				return true // on a horizontal boundary
			}
		}

		if p1.X == p2.X && p1.X == testPoint.X {
			minY := min(p1.Y, p2.Y)
			maxY := max(p1.Y, p2.Y)
			if testPoint.Y >= minY && testPoint.Y <= maxY {
				return true // on a vertical boundary
			}
		}

		if (p1.Y <= testPoint.Y && testPoint.Y < p2.Y) || (p2.Y <= testPoint.Y && testPoint.Y < p1.Y) {
			if p1.X == p2.X {
				if p1.X > testPoint.X {
					crossings++
				}
			}
		}
	}

	return crossings%2 == 1 // odd crossings = inside
}
