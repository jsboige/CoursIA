# QC MCP Lite

Lightweight MCP server for QuantConnect API — ~10 tools, <5k tokens schema.

Replaces the heavy `quantconnect/mcp-server` Docker container (~40k tokens) for standard backtesting workflows.

## Tools

| Tool | Description |
|------|-------------|
| `create_compile` | Create a compile job |
| `read_compile` | Read compile status |
| `create_backtest` | Create a backtest from compiled project |
| `read_backtest` | Read backtest results (Sharpe, CAGR, MaxDD) |
| `list_backtests` | List backtests for a project |
| `list_projects` | List all QC projects |
| `read_project` | Read project details and files |
| `read_file` | Read file(s) from a project |
| `update_file_contents` | Update a file in a project |
| `create_file` | Create a new file in a project |

## Setup

### 1. Set environment variables

```bash
export QC_API_USER_ID="your_user_id"
export QC_API_ACCESS_TOKEN="your_api_token"
```

Or add to your `.env` file (gitignored).

### 2. Configure in `.mcp.json`

Replace the Docker-based `qc-mcp` with:

```json
{
  "mcpServers": {
    "qc-mcp-lite": {
      "command": "python",
      "args": ["scripts/qc-mcp-lite/server.py"],
      "env": {
        "QC_API_USER_ID": "your_user_id",
        "QC_API_ACCESS_TOKEN": "your_api_token"
      }
    }
  }
}
```

### 3. Verify

```bash
python -c "from server import list_projects; print(list_projects())"
```

## Auth

Uses the QC API v2 authentication pattern:
- `SHA256(token:timestamp)` hash
- `Basic userId:hash` authorization header
- `Timestamp` header

## Rate Limiting

10 calls/min enforced in-process. Matches the fleet-wide QC API rate limit.

## Reverting to Full MCP

To switch back to the official Docker MCP:

```json
{
  "mcpServers": {
    "qc-mcp": {
      "command": "docker",
      "args": ["run", "-i", "--rm",
        "-e", "QUANTCONNECT_USER_ID=46613",
        "-e", "QUANTCONNECT_API_TOKEN=your_token",
        "-e", "AGENT_NAME=claude-code",
        "quantconnect/mcp-server"
      ]
    }
  }
}
```
