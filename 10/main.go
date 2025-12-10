package main

import (
	"fmt"
	"os"
	"os/exec"
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
	c := 0
	prefix := "test"
	if !aoc.DebugMode {
		prefix = "solve"
	}

	ans := 0

	for line := range aoc.LinesFromFile(os.Args[2]) {
		filename := fmt.Sprintf("10/%s-%02d.smt2", prefix, c)
		f, err := os.Create(filename)
		aoc.Fail(err)
		c++

		fields := strings.Fields(line)
		numberOfButtons := len(fields) - 2
		for i := 0; i < numberOfButtons; i++ {
			fmt.Fprintf(f, "(declare-const b%d Int)\n", i)
		}
		fmt.Fprintln(f, "")

		for i := 0; i < numberOfButtons; i++ {
			fmt.Fprintf(f, "(assert (>= b%d 0))\n", i)
		}
		fmt.Fprintln(f, "")

		targetJoltages := aoc.IntsFromString(fields[len(fields)-1])
		buttonsPerJoltage := make([][]int, len(targetJoltages))
		for i := range targetJoltages {
			buttonsPerJoltage[i] = []int{}
		}

		for i := 1; i < len(fields)-1; i++ {
			buttons := aoc.IntsFromString(fields[i])
			for _, button := range buttons {
				buttonsPerJoltage[button] = append(buttonsPerJoltage[button], i-1)
			}
		}

		for joltage, buttons := range buttonsPerJoltage {
			fmt.Fprintf(f, "; ")
			fmt.Fprintf(f, "%s", strings.Join(aoc.Map(buttons, func(b int) string {
				return fmt.Sprintf("b%d", b)
			}), " + "))
			fmt.Fprintf(f, " = %d\n", targetJoltages[joltage])

			fmt.Fprintf(f, "(assert (= (+")
			for _, button := range buttons {
				fmt.Fprintf(f, " b%d", button)
			}
			fmt.Fprintf(f, ") %d))\n", targetJoltages[joltage])

			fmt.Fprintln(f, "")
		}

		allButtons := make([]string, numberOfButtons)
		for i := 0; i < numberOfButtons; i++ {
			allButtons[i] = fmt.Sprintf("b%d", i)
		}

		fmt.Fprintf(f, "(minimize (+ %s))\n\n", strings.Join(allButtons, " "))

		fmt.Fprintln(f, "(check-sat)")
		fmt.Fprintln(f, "(get-model)")
		fmt.Fprintf(f, "(get-value ((+ %s)))\n", strings.Join(allButtons, " "))

		f.Close()

		cmd := exec.Command("./z3/bin/z3", filename)
		output, err := cmd.CombinedOutput()
		aoc.Fail(err)
		lines := strings.Split(strings.TrimSpace(string(output)), "\n")
		ints := aoc.IntsFromString(lines[len(lines)-1])
		minimumNumberOfPresses := ints[len(ints)-1]
		aoc.Debug(minimumNumberOfPresses)
		ans += minimumNumberOfPresses

		if !aoc.DebugMode {
			err := os.Remove(filename)
			aoc.Fail(err)
		}
	}

	fmt.Println("")
	fmt.Println(ans)
}
