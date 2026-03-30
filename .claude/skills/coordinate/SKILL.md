---
name: coordinate
description: Resume multi-agent coordination session. Reads memory, RooSync inbox, GitHub issues, and produces a situational briefing with recommended actions. Arguments: [--dispatch] [--focus <topic>] [--reply-all]
---

# Skill: Coordinate - Multi-Agent Coordination Hub

Resume or start a coordination session across all agents working on the CoursIA repository.

**Target**: `$ARGUMENTS`

## Arguments

- (no args): Full situational briefing (memory + RooSync + issues)
- `--dispatch`: After briefing, propose and send task assignments to idle agents via RooSync
- `--focus <topic>`: Focus on a specific area: `qc`, `slides`, `smartcontracts`, `sudoku`, `genai`, `epita`
- `--reply-all`: Read all unread RooSync messages and draft replies

## Process

### Phase 1 - Load Context from Memory

Read the following memory files to restore full situational awareness:

1. `~/.claude/projects/d--CoursIA/memory/MEMORY.md` - Index + quick reference
2. `~/.claude/projects/d--CoursIA/memory/agent_map.md` - Agent statuses + RooSync IDs
3. `~/.claude/projects/d--CoursIA/memory/teaching_schedule_2026.md` - Deadlines + priorities
4. `~/.claude/projects/d--CoursIA/memory/jared_qc_partnership.md` - QC sponsorship context (if --focus qc)

### Phase 2 - Gather Live State

1. **RooSync inbox**: `roosync_read(mode: "inbox", status: "unread")` - Check for new messages from agents
2. **GitHub issues**: `gh issue list --state open --limit 30 --json number,title,labels` - Current open issues
3. **Git status**: `git log --oneline -5` - Recent commits on main
4. **PRs**: `gh pr list --state open` - Any pending PRs to review

### Phase 3 - Produce Situational Briefing

Output a structured briefing:

```markdown
# Coordination Briefing - [DATE]

## Deadlines
- [Next 3 deadlines with countdown]

## Agent Status
| Agent | Status | Last Activity | Pending Questions |
|-------|--------|---------------|-------------------|

## Unread Messages
- [Summary of unread RooSync messages, if any]

## Open Issues (relevant)
- [Top issues by priority, filtered by --focus if provided]

## Recommended Actions
1. [Prioritized list of what to do next]
```

### Phase 4 - Dispatch (if --dispatch)

For each idle agent with a clear next task:

1. Compose a directive message with:
   - Clear task description
   - Issue number reference
   - Expected deliverables (branch name, PR)
   - Quality criteria
2. Send via `roosync_send` to the agent's RooSync ID
3. Log the dispatch in the briefing output

### Phase 5 - Reply All (if --reply-all)

For each unread message:
1. Read full message content
2. Draft appropriate reply (answer questions, acknowledge status, assign next task)
3. Present replies to user for approval before sending
4. Mark messages as read after processing

## RooSync Communication Patterns

### Sending directives
```
roosync_send(
  to: "<machine>:<workspace>",
  subject: "[DIRECTIVE] <short description>",
  body: "## Mission\n...\n## Deliverables\n...\n## Quality Criteria\n...",
  priority: "MEDIUM",
  tags: ["directive", "<topic>"]
)
```

### Acknowledging status reports
```
roosync_send(
  action: "reply",
  message_id: "<original-msg-id>",
  body: "Recu. [feedback/next steps]",
  priority: "MEDIUM"
)
```

## Focus Areas

### qc (QuantConnect)
- Agent: po-2024
- Issues: #106-113, #81
- Context: ESGF deadline fin mars, Sprint 1 done, Sprint 2 pending
- Memory: jared_qc_partnership.md, qc_strategies_catalog.md

### slides
- Agent: po-2025
- Deadline: 24 mars CM ECE
- Context: PPTX migration, Marp attempt failed previously

### smartcontracts
- Agents: po-2023:CoursIA, po-2026
- Issues: #119, #129
- Deadline: 20 mai EPITA
- Context: Plan complet existe (26 notebooks, execution reelle)

### sudoku / search
- Agents: po-2023:CoursIA, po-2026
- Deadline: mi-avril EPITA
- Context: Search/CSP done (PR #127), Sudoku a reviser

### genai
- Agent: po-2023:GenAI_Series
- Issues: #49, #60, #78, #79, #80, #84
- Context: 14/20 SemanticKernel OK, 6 echecs diagnostiques

### epita
- Issues: #55 (IA Symbolique), Search/Sudoku
- Deadlines: mi-avril (contraintes), 20 mai (symbolique)
- Context: Tweety/Planners/SC enrichis, Lean-9/SW-13 done

## Important Rules

- **Never force push** - See CLAUDE.md rules
- **Coordination via RooSync only** - No coordination files in git
- **po-2023 has TWO workspaces** - GenAI_Series vs CoursIA, never conflate
- **Issues + PRs** - Each task = issue, each delivery = PR with review
- **Prioritize by deadline** - QC/slides > SmartContracts > Sudoku > GenAI
