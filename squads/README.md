# Premium Squads

Pre-built agent squads installed during `npx aiox-core install` after Pro license activation.

## Available Squads

| Squad | Agents | Description |
|-------|--------|-------------|
| **squad-creator-pro** | 3 | Meta-squad for creating AI agent squads based on real elite minds |
| **design** | 8 | Design System squad — tokens, components, accessibility, DesignOps |

## How It Works

1. User runs `npx aiox-core install` and activates Pro license
2. `@aiox-fullstack/pro` npm package is installed
3. Scaffolder copies all squads from this directory into the user's project `squads/`
4. Agent commands are auto-installed into active IDEs (Claude Code, Codex, Gemini, Cursor)

## Adding New Squads

1. Develop in `pro/private-squads/` (not published)
2. When ready, move to `pro/squads/`
3. Add to `package.json` `files` array
4. Bump version and publish
