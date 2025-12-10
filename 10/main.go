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

type Machine struct {
	TargetState int   // bitmask
	Buttons     []int // bitmasks
	Joltages    []int
}

type State struct {
	Mask    int
	History []int
}

func part1() {
	var machines []Machine

	for line := range aoc.LinesFromFile(os.Args[2]) {
		fields := strings.Fields(line)
		indicatorLights := strings.Split(strings.Trim(fields[0], "[]"), "")
		targetState := 0
		for i, light := range indicatorLights {
			if light == "#" {
				targetState |= (1 << i)
			}
		}
		machine := Machine{
			TargetState: targetState,
			Buttons:     []int{},
			Joltages:    aoc.IntsFromString(fields[len(fields)-1]),
		}

		for i := 1; i < len(fields)-1; i++ {
			buttons := aoc.IntsFromString(fields[i])
			mask := 0
			for _, button := range buttons {
				mask |= (1 << button)
			}
			machine.Buttons = append(machine.Buttons, mask)
		}

		machines = append(machines, machine)
	}

	ans := 0

	for _, machine := range machines {
		queue := []State{{Mask: 0, History: []int{}}}
		visited := make(map[int]bool)
		visited[0] = true
		for len(queue) > 0 {
			current := queue[0]
			queue = queue[1:]

			if current.Mask == machine.TargetState {
				ans += len(current.History)
				break
			}

			for i, buttonMask := range machine.Buttons {
				nextMask := current.Mask ^ buttonMask

				if !visited[nextMask] {
					visited[nextMask] = true

					newHistory := make([]int, len(current.History))
					copy(newHistory, current.History)
					newHistory = append(newHistory, i)

					queue = append(queue, State{
						Mask:    nextMask,
						History: newHistory,
					})
				}
			}
		}
	}

	fmt.Println(ans)
}

func part2() {
	for line := range aoc.LinesFromFile(os.Args[2]) {
		fmt.Println(line)
	}
}
