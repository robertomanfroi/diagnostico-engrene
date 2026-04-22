# Task: Diagnose Story Using Story Grid Methodology

**Task ID:** diagnose-story-grid
**Version:** 1.0.0
**Agent:** @shawn-coyne
**Mode:** Interactive (Guided Diagnostic)
**Duration:** 30-60 minutes depending on scope

---

## Overview

This task guides writers through a complete Story Grid diagnostic of their manuscript or story, systematically identifying structural problems and providing specific, actionable fixes. The process mirrors how veteran editor Shawn Coyne would approach manuscript evaluation.

> "The Story Grid is like a CT Scan that takes a photo of the global story and tells the editor or writer what is working, what is not."
> — Shawn Coyne

---

## Inputs

| Parameter | Type | Required | Description | Example |
|-----------|------|----------|-------------|---------|
| `story_title` | string | Yes | Title of the work | "The Shadow Protocol" |
| `story_summary` | string | Yes | 2-3 paragraph summary | "A spy discovers..." |
| `word_count` | number | No | Approximate length | 80000 |
| `draft_status` | string | No | Current draft stage | "first draft", "revision" |
| `specific_concern` | string | No | Writer's main worry | "Middle feels slow" |
| `scenes_available` | boolean | No | Can provide scene list? | true/false |

---

## Preconditions

- [ ] Writer has a completed draft OR detailed outline
- [ ] Writer can provide story summary with beginning, middle, end
- [ ] Writer is ready for honest, direct feedback
- [ ] Understanding: We diagnose the Story, not the person

---

## The Story Grid Diagnostic Framework

### Core Principle

> "If you start fixing before you have a complete diagnosis of all of your problems, you'll inevitably drive yourself crazy. Bailing out water from your leaky boat before you discover where the big hole is just burns precious time and energy. Inspect every part of the boat first to find out where the big and small holes are. Fix the big ones, then work your way down."
> — Shawn Coyne

---

## PHASE 1: GENRE IDENTIFICATION (The Foundation)

### Duration: 5-10 minutes

### Why Genre First

> "Deciding what Genre(s) your Story will inhabit will tell you exactly what you need to do to satisfy your potential audience's expectations. You must know what your reader is expecting before you can possibly satisfy her."
> — Shawn Coyne

Genre is not a marketing category—it's a promise to the reader. Every genre comes with specific conventions (setup elements) and obligatory scenes (must-have moments). Miss these, and you break the reader's trust.

### Step 1.1: Apply the Genre Five-Leaf Clover

**ELICIT FROM WRITER:**

```
I need to classify your story's genre using the Story Grid Five-Leaf Clover.
Please answer these questions:

1. TIME GENRE - How long will it take to consume?
   a) Short Story (under 7,500 words)
   b) Novella (7,500-40,000 words)
   c) Novel (40,000-200,000 words)
   d) Series (multiple books)

2. STRUCTURE GENRE - What's your narrative structure?
   a) Archplot (single protagonist, clear causality, closed ending)
   b) Miniplot (internal focus, ambiguous resolution)
   c) Antiplot (coincidence, non-linear time, inconsistent reality)

3. REALITY GENRE - How much must readers suspend disbelief?
   a) Factualism (real world, true events - memoir, biography)
   b) Realism (real world, fictional events)
   c) Fantasy (alternate world with different rules)
   d) Absurdism (reality defies logical explanation)

4. STYLE GENRE - What's the emotional tone?
   a) Drama (serious treatment, generates tears or tension)
   b) Comedy (light treatment, generates laughter)

5. CONTENT GENRE - What's the CORE story about?
   This is the most important leaf. Choose PRIMARY genre:

   EXTERNAL GENRES (plot-driven):
   a) Action - Will protagonist survive? (Life/Death)
   b) Horror - Can they escape the monster/evil? (Self-preservation)
   c) Thriller - Can they stop evil from winning? (Life/Fate worse than death)
   d) Crime - Will justice be served? (Justice/Injustice)
   e) Western - Will freedom be won? (Freedom/Oppression)
   f) War - Will honor be preserved? (Honor/Dishonor)
   g) Love - Will they find love? (Love/Hate)
   h) Performance - Will they earn respect? (Respect/Shame)
   i) Society - Will the group survive? (Power/Impotence)

   INTERNAL GENRES (character-driven):
   j) Status - Will they succeed or fail? (Success/Failure)
   k) Worldview - Will they gain wisdom? (Sophistication/Naivete)
   l) Morality - Will they choose good? (Altruism/Selfishness)
```

### Step 1.2: Identify Internal Genre (If External Primary)

Most novels have BOTH an external and internal genre. The external drives the plot; the internal drives the character arc.

**ELICIT:**

```
You've identified your EXTERNAL genre as [GENRE].
Now let's identify the INTERNAL genre - the character's inner journey.

What internal change does your protagonist undergo?

WORLDVIEW subgenres:
a) Maturation - naive → sophisticated understanding of world
b) Education - meaninglessness → finding meaning
c) Disillusionment - belief → loss of faith
d) Revelation - ignorance → self-knowledge

MORALITY subgenres:
e) Testing - willpower tested against temptation
f) Punitive - good person becomes evil, faces punishment
g) Redemption - selfish → altruistic

STATUS subgenres:
h) Admiration - underdog rises to success
i) Tragic - success → failure through character flaw
```

### Step 1.3: Record Genre Classification

**OUTPUT:**

```yaml
genre_classification:
  time: [Novel/Novella/etc]
  structure: [Archplot/Miniplot/Antiplot]
  reality: [Realism/Fantasy/etc]
  style: [Drama/Comedy]
  external_content: [Primary external genre]
  internal_content: [Internal genre if applicable]
  subgenre: [Specific subgenre]
```

### Step 1.4: List Obligatory Scenes and Conventions

Based on the identified genre(s), generate the list of required elements.

**For each Content Genre, identify:**

| Element | Description | Present? |
|---------|-------------|----------|
| **Conventions** | Setup elements creating expectations | |
| **Obligatory Scenes** | Must-have moments paying off conventions | |

**Example for THRILLER:**

```yaml
thriller_requirements:
  conventions:
    - Crime occurs early with clue about villain's MacGuffin
    - Speech in praise of the villain
    - MacGuffin that everyone is after
    - Clear villain with comprehensible methodology
    - Ticking clock or deadline

  obligatory_scenes:
    - Hero discovers/commits to stopping villain
    - Hero's initial strategy fails
    - Hero at mercy of villain (seemingly no escape)
    - False ending (villain reasserts)
    - Hero confronts villain in final battle
    - Evil is exposed/defeated
```

**Example for LOVE:**

```yaml
love_requirements:
  conventions:
    - Obstacle keeping lovers apart
    - Triangle (external temptation for one or both)
    - Helpers and harmers
    - Secrets that could destroy relationship

  obligatory_scenes:
    - Lovers meet
    - First kiss/intimate moment
    - Confession of love
    - Lovers break up
    - Proof of love (sacrifice)
    - Lovers reunite (or don't in tragic)
```

---

## PHASE 2: GLOBAL STORY ANALYSIS (The Foolscap)

### Duration: 10-15 minutes

### Why Foolscap First

The Foolscap Global Story Grid gives us the 30,000 foot view. Before we examine individual scenes, we need to understand if the GLOBAL structure works. A brilliant scene cannot save a broken global structure.

### Step 2.1: Map the Three Movements

**ELICIT:**

```
Let's map your story's three main movements.

BEGINNING HOOK (First 25% of story)
This section HOOKS the reader, establishes the genre, and makes promises.

1. What is the INCITING INCIDENT that throws your protagonist's life out of balance?
   (The event that starts everything)

2. What PROGRESSIVE COMPLICATIONS arise? What's the TURNING POINT?
   (Problems that escalate, culminating in a moment that changes direction)

3. What CRISIS does your protagonist face at the end of Act 1?
   (A true dilemma - not a no-brainer)

4. What is the CLIMAX - how do they respond to the crisis?
   (Their active choice/action)

5. What is the RESOLUTION - the new status quo?
   (Where things stand after their choice)
```

**Repeat for MIDDLE BUILD (50%) and ENDING PAYOFF (25%)**

### Step 2.2: Validate Global Five Commandments

**CHECK EACH MOVEMENT:**

| Movement | Inciting Incident | Turning Point | Crisis | Climax | Resolution |
|----------|-------------------|---------------|--------|--------|------------|
| Beginning Hook | _____ | _____ | _____ | _____ | _____ |
| Middle Build | _____ | _____ | _____ | _____ | _____ |
| Ending Payoff | _____ | _____ | _____ | _____ | _____ |

### Step 2.3: Check Critical Connections

**Diagnostic Questions:**

1. **Inciting Incident → Climax Connection**
   > "The inciting incident must promise the climactic action. In turn, the climax must mirror the inciting incident to show how the protagonist has changed."

   Does your global inciting incident CONNECT to your global climax?
   - [ ] YES - The climax pays off what the inciting incident promised
   - [ ] NO - These feel disconnected (MAJOR PROBLEM)

2. **Progressive Build**
   Do complications ESCALATE from Beginning Hook through Middle Build to Ending Payoff?
   - [ ] YES - Stakes continuously rise
   - [ ] NO - Middle sags or stakes plateau (COMMON PROBLEM)

3. **Crisis Quality**
   Is the global crisis a TRUE DILEMMA?
   - [ ] Best Bad Choice (two terrible options)
   - [ ] Irreconcilable Goods (two great options, can only have one)
   - [ ] Neither / No-brainer (PROBLEM - no real tension)

### Step 2.4: Extract Controlling Idea

**ELICIT:**

```
The Controlling Idea is a single sentence stating how the core value changes and why.

Formula: [VALUE] prevails when we choose [ACTION]

Based on your ending:
1. Does your protagonist achieve their goal? (Positive or Negative ending)
2. What VALUE is at stake? (From your genre's core value)
3. What ACTION/CHOICE leads to that outcome?

Draft your Controlling Idea:
"_____________ prevails when we choose to _____________."
```

**Validate Against Genre:**

- Does this controlling idea align with your genre's core value?
- Is it specific enough? (Not generic like "good wins")
- Does it emerge from the story's climactic choice?

### Step 2.5: Complete Foolscap Document

**OUTPUT:**

```markdown
# FOOLSCAP GLOBAL STORY GRID

**Story Title:** [Title]
**External Genre:** [Genre]
**Internal Genre:** [Genre]
**Controlling Idea:** [Statement]

## GLOBAL STRUCTURE

### BEGINNING HOOK (25%)
- **Inciting Incident:** [Event that destabilizes]
- **Progressive Complications:** [List of escalating problems]
- **Turning Point:** [Moment that forces crisis]
- **Crisis:** [The dilemma faced]
- **Climax:** [The choice/action taken]
- **Resolution:** [New status quo]

### MIDDLE BUILD (50%)
- **Inciting Incident:** [Event that launches middle]
- **Progressive Complications:** [Escalating problems]
- **Turning Point:** [All-is-lost moment or equivalent]
- **Crisis:** [Major dilemma]
- **Climax:** [Critical choice]
- **Resolution:** [Sets up final confrontation]

### ENDING PAYOFF (25%)
- **Inciting Incident:** [Event launching finale]
- **Progressive Complications:** [Final escalations]
- **Turning Point:** [Moment of truth]
- **Crisis:** [Ultimate dilemma]
- **Climax:** [Final choice/confrontation]
- **Resolution:** [New equilibrium - ending]

## OBLIGATORY SCENES CHECK
- [ ] [Scene 1]
- [ ] [Scene 2]
- [Continue for all genre obligations]

## CONVENTIONS CHECK
- [ ] [Convention 1]
- [ ] [Convention 2]
- [Continue for all conventions]
```

---

## PHASE 3: OBLIGATORY SCENES AUDIT

### Duration: 5-10 minutes

### Why This Matters

> "Ditching the Conventions and Obligatory Moments cannot ever be an option. Your reader matters too much. If you cheap out on her, she'll never trust you with a story again."
> — Shawn Coyne

Missing obligatory scenes is one of the most common reasons stories fail to satisfy readers. They may not consciously know WHAT's missing, but they feel disappointed.

### Step 3.1: Check External Genre Obligations

**ELICIT:**

```
Let's verify your [EXTERNAL GENRE] obligatory scenes are present.

For each required scene, tell me:
- Is it in your story? (Yes/No)
- If yes, which scene/chapter?
- If no, why not?

[Present genre-specific list]
```

### Step 3.2: Check Internal Genre Obligations

If the story has an internal genre, verify those obligations too.

**Example for MORALITY-REDEMPTION:**

```yaml
morality_redemption_check:
  conventions:
    - [ ] Protagonist begins in selfishness
    - [ ] Ghost from past haunts protagonist
    - [ ] Aide/mentor figure
    - [ ] Opportunity for selfless act

  obligatory_scenes:
    - [ ] Protagonist actively harms others through selfishness
    - [ ] Moment of grace/realization
    - [ ] Choice to sacrifice self-interest
    - [ ] Proof of transformation through action
```

### Step 3.3: Record Missing Elements

**OUTPUT:**

```yaml
obligatory_audit:
  present:
    - [List scenes that ARE in the story]

  missing:
    - scene: "[Missing scene]"
      impact: "HIGH/MEDIUM"
      recommendation: "[How to add]"

  weak:
    - scene: "[Scene that exists but is underdeveloped]"
      problem: "[What's wrong]"
      recommendation: "[How to strengthen]"
```

---

## PHASE 4: SCENE-LEVEL ANALYSIS (The Spreadsheet)

### Duration: 15-30 minutes (depends on detail level)

### Why Scene Analysis

> "Scenes are the fundamental building blocks of Fiction. If scenes don't work, the story doesn't work."
> — Shawn Coyne

Every scene must contain the Five Commandments and demonstrate a value shift. Scenes without these elements are exposition, not story.

### Step 4.1: Select Analysis Approach

**ELICIT:**

```
For scene-level analysis, choose an approach:

1. FULL SPREADSHEET - Analyze every scene (most thorough, longest)
2. SAMPLE ANALYSIS - Analyze key scenes from each movement
3. PROBLEM SCENES - Focus on scenes writer suspects are broken
4. TURNING POINT CHECK - Verify variety in turning points across story

Which approach works for your diagnostic?
```

### Step 4.2: Scene Analysis Template

For each scene analyzed:

```yaml
scene_analysis:
  scene_number: X
  scene_name: "[Name/Chapter]"
  word_count: [approximate]
  pov_character: "[Name]"

  # THE FIVE COMMANDMENTS
  inciting_incident:
    event: "[What happens]"
    type: "causal/coincidental"
    present: true/false

  progressive_complications:
    complications: "[List problems that arise]"
    turning_point:
      event: "[The turning moment]"
      type: "action/revelation"
    present: true/false

  crisis:
    question: "[The dilemma]"
    type: "best_bad_choice/irreconcilable_goods"
    stakes: "[What's at risk]"
    present: true/false

  climax:
    action: "[What protagonist does]"
    present: true/false

  resolution:
    outcome: "[Result of climax]"
    present: true/false

  # VALUE ANALYSIS
  value_at_start: "[Value + polarity]"
  value_at_end: "[Value + polarity]"
  polarity_shift: "+/- or -/+ or -/-- etc"
  value_shift_present: true/false

  # DIAGNOSIS
  working: true/false
  problems:
    - "[Problem 1]"
    - "[Problem 2]"
  recommendations:
    - "[Fix 1]"
    - "[Fix 2]"
```

### Step 4.3: Value Shift Deep Dive

For each scene, verify value shifts:

**The Core Four Values (Genre-Specific):**

```
[POSITIVE] → [CONTRARY] → [NEGATIVE] → [NEGATION OF NEGATION]
    (+)           (-)          (--)              (---)
```

**Example for ACTION genre:**

```
LIFE → Unconsciousness → Death → FATE WORSE THAN DEATH
 (+)        (-)           (--)           (---)
```

**Diagnostic Questions:**
1. What value is at stake in this scene?
2. Where on the spectrum does the scene START?
3. Where on the spectrum does the scene END?
4. Did polarity shift? (+ to - or - to +)

> "If there's no change in value, the scene doesn't work. If you can't identify the turning point, then the value shift is probably not strong enough."
> — Shawn Coyne

### Step 4.4: Turning Point Variety Check

Track turning point types across ALL scenes:

```yaml
turning_point_analysis:
  action_turns: [count]
  revelation_turns: [count]
  ratio: "[X action : Y revelation]"

  pattern_problems:
    - "Scenes 5-12 all use revelation turns"
    - "No action turns in Middle Build"

  recommendation: |
    Variety in turning points keeps readers engaged.
    "If you are turning your scenes the same way over and over again,
    repetitious turns will turn off a reader or viewer subconsciously."
    Mix action and revelation throughout.
```

### Step 4.5: Crisis Quality Check

For each major crisis (scene, sequence, act, global):

```yaml
crisis_audit:
  - location: "End of Beginning Hook"
    crisis_question: "[The dilemma]"
    type: "best_bad_choice/irreconcilable_goods/no_brainer"
    stakes_clear: true/false
    forces_active_choice: true/false
    quality: "STRONG/WEAK/MISSING"

  # If WEAK or NO_BRAINER:
  problem: "[Why it doesn't work]"
  recommendation: "[How to strengthen]"
```

---

## PHASE 5: PROBLEM COMPILATION AND PRIORITIZATION

### Duration: 5-10 minutes

### The Prioritization Principle

Not all problems are equal. Global problems cascade down to affect everything. Fix top-down.

### Step 5.1: Categorize All Identified Problems

```yaml
problems_identified:

  global_level: # Fix these FIRST
    - problem: "[Description]"
      impact: "HIGH"
      location: "[Where in story]"
      fix_complexity: "HIGH/MEDIUM/LOW"

  act_sequence_level: # Fix these SECOND
    - problem: "[Description]"
      impact: "MEDIUM-HIGH"
      location: "[Which act/sequence]"
      fix_complexity: "HIGH/MEDIUM/LOW"

  scene_level: # Fix these THIRD
    - problem: "[Description]"
      impact: "LOW-MEDIUM"
      location: "[Which scene]"
      fix_complexity: "HIGH/MEDIUM/LOW"

  missing_obligations: # Critical
    - "[Obligatory scene/convention missing]"

  pattern_problems: # Systemic issues
    - "[Repetitive turns, flat crises, etc]"
```

### Step 5.2: Create Problem Hierarchy

**OUTPUT:**

```markdown
# DIAGNOSTIC REPORT: [Story Title]

## CRITICAL PROBLEMS (Must Fix First)
1. [Global-level problem]
2. [Missing obligatory scene]
3. [Genre mismatch]

## MAJOR PROBLEMS (Fix After Critical)
1. [Act-level issue]
2. [Sequence-level issue]
3. [Pattern problem]

## MODERATE PROBLEMS (Fix After Major)
1. [Scene-level issue]
2. [Value shift weakness]
3. [Crisis quality issue]

## MINOR PROBLEMS (Polish Phase)
1. [Individual scene tweaks]
2. [Variety improvements]
```

---

## PHASE 6: PRESCRIPTION (Specific Fixes)

### Duration: 10-15 minutes

### Fix Philosophy

> "The Story Grid pinpoints story problems but does not emotionally abuse the writer, revealing exactly where a Story (not the person creating the Story... the Story) has failed."
> — Shawn Coyne

Every problem gets a specific, actionable fix. No vague "make it better."

### Step 6.1: Critical Problem Fixes

For each CRITICAL problem:

```yaml
fix_prescription:
  problem: "[Clear description of problem]"
  why_critical: "[Why this must be fixed first]"

  diagnosis:
    what_broken: "[Specific element that's broken]"
    why_broken: "[Root cause]"
    impact: "[How it affects rest of story]"

  prescription:
    action: "[Specific action to take]"
    example: "[What this might look like]"
    checklist:
      - "[ ] Step 1"
      - "[ ] Step 2"
      - "[ ] Step 3"

  validation:
    how_to_test: "[How to verify fix worked]"
```

### Step 6.2: Missing Obligatory Scene Fixes

For each missing obligation:

```yaml
obligatory_fix:
  missing: "[Scene/convention name]"
  genre_requirement: "[Why genre requires this]"

  where_to_add: "[Recommended location in story]"
  how_to_create:
    purpose: "[What this scene must accomplish]"
    value_at_stake: "[What value shifts]"
    example_approaches:
      - "[Approach 1]"
      - "[Approach 2]"

  innovation_notes: |
    Don't just copy generic version of this scene.
    "If you rehash something you saw on a Mannix episode from the 1970s,
    you will sorely disappoint your reader."
    Innovate within the obligation.
```

### Step 6.3: Five Commandments Fixes

For scenes missing commandments:

```yaml
commandment_fix:
  scene: "[Scene identifier]"
  missing: "[Which commandment(s)]"

  # For each missing commandment:
  inciting_incident_fix:
    problem: "No clear event destabilizes the scene"
    solution: "Add [specific event] that throws [character]'s immediate goal off balance"

  progressive_complication_fix:
    problem: "Complications don't escalate / No clear turning point"
    solution: "Build [problem 1] → [problem 2] → [turning point moment]"

  crisis_fix:
    problem: "No real dilemma / no-brainer choice"
    solution: "Force choice between [option A] and [option B], both with real stakes"

  climax_fix:
    problem: "Character doesn't actively respond to crisis"
    solution: "Character must take action: [specific action]"

  resolution_fix:
    problem: "No new status quo established"
    solution: "Show consequence of climax: [new situation]"
```

### Step 6.4: Value Shift Fixes

For scenes with weak/no value shifts:

```yaml
value_shift_fix:
  scene: "[Scene identifier]"
  current_problem: "[No shift / unclear shift / wrong value]"

  prescription:
    value_to_track: "[Genre-appropriate value]"
    start_polarity: "[+ or -]"
    end_polarity: "[opposite of start]"
    turning_point_moment: "[Where shift happens]"

  implementation:
    - "Open scene with clear establishment of [value at start polarity]"
    - "Build complications that threaten the value"
    - "Turning point [action/revelation] that flips polarity"
    - "Close scene with character in new position on value spectrum"
```

---

## PHASE 7: REVISION ROADMAP

### Duration: 5 minutes

### Step 7.1: Create Ordered Fix List

**OUTPUT:**

```markdown
# REVISION ROADMAP: [Story Title]

## ROUND 1: Critical Fixes (Do these first)
- [ ] Fix: [Problem 1] → [Specific action]
- [ ] Fix: [Problem 2] → [Specific action]
- [ ] Add: [Missing obligatory scene] in [location]

## ROUND 2: Major Fixes (After Round 1 complete)
- [ ] Fix: [Act problem] → [Specific action]
- [ ] Strengthen: [Weak sequence] → [How]
- [ ] Address: [Pattern problem] → [How]

## ROUND 3: Scene Fixes (After Round 2 complete)
- [ ] Scene X: [Fix needed]
- [ ] Scene Y: [Fix needed]
- [ ] Scene Z: [Fix needed]

## ROUND 4: Polish (After major fixes)
- [ ] Verify all value shifts
- [ ] Check turning point variety
- [ ] Validate all Five Commandments

## RE-DIAGNOSIS
After completing Round 1-2, run diagnostic again.
Global fixes may resolve or change scene-level issues.
```

### Step 7.2: Set Expectations

```markdown
## WHAT TO EXPECT

After implementing these fixes:
- Your story will meet genre expectations
- Readers will feel satisfied (obligations paid off)
- Each scene will WORK (value shifts, commandments present)
- The global structure will support your themes

Remember:
- Fix biggest problems first (they cascade)
- Re-diagnose after major changes
- Innovation happens WITHIN obligations, not instead of them
- The reader matters most
```

---

## FINAL OUTPUT: COMPLETE DIAGNOSTIC REPORT

### Template

```markdown
# STORY GRID DIAGNOSTIC REPORT

**Story:** [Title]
**Author:** [Name]
**Date:** [Date]
**Diagnostic Agent:** @shawn-coyne

---

## GENRE CLASSIFICATION

| Leaf | Classification |
|------|----------------|
| Time | [Novel/etc] |
| Structure | [Archplot/etc] |
| Reality | [Realism/etc] |
| Style | [Drama/Comedy] |
| External Content | [Genre] |
| Internal Content | [Genre] |
| Subgenre | [Specific] |

**Controlling Idea:** [Statement]

---

## GLOBAL STRUCTURE ANALYSIS

### Beginning Hook
[Summary with Five Commandments]

### Middle Build
[Summary with Five Commandments]

### Ending Payoff
[Summary with Five Commandments]

**Global Structure Grade:** [WORKING / NEEDS WORK / BROKEN]

---

## OBLIGATORY SCENES AUDIT

### Present (✓)
- [Scene 1]
- [Scene 2]

### Missing (✗)
- [Scene - with recommendation]

### Weak (!)
- [Scene - with fix needed]

**Obligations Grade:** [COMPLETE / GAPS / SIGNIFICANT GAPS]

---

## SCENE ANALYSIS SUMMARY

**Total Scenes Analyzed:** [X]
**Working Scenes:** [X]
**Scenes Needing Work:** [X]

### Common Issues Found
- [Issue 1 - frequency]
- [Issue 2 - frequency]

### Turning Point Variety
- Action turns: [X]
- Revelation turns: [X]
- Assessment: [Varied / Repetitive]

**Scene-Level Grade:** [STRONG / ADEQUATE / WEAK]

---

## PROBLEMS IDENTIFIED

### Critical (Fix Immediately)
1. [Problem + Location]
2. [Problem + Location]

### Major (Fix After Critical)
1. [Problem + Location]

### Moderate (Fix After Major)
1. [Problem + Location]

### Minor (Polish Phase)
1. [Problem + Location]

---

## REVISION ROADMAP

### Round 1: Critical Fixes
- [ ] [Action 1]
- [ ] [Action 2]

### Round 2: Major Fixes
- [ ] [Action 1]

### Round 3: Scene Fixes
- [ ] [Action per scene]

### Round 4: Polish
- [ ] Final validation

---

## SUMMARY

**Overall Assessment:** [Brief narrative summary]

**Biggest Strength:** [What's working well]

**Biggest Opportunity:** [Most impactful fix]

**Estimated Revision Effort:** [Light / Moderate / Substantial / Major overhaul]

---

*Diagnostic performed using Shawn Coyne's Story Grid Methodology*
*"The Story Grid is like a CT Scan that reveals what is working, what is not."*
```

---

## ERROR HANDLING

### Common Diagnostic Challenges

| Challenge | Response |
|-----------|----------|
| Writer can't identify genre | Use questioning to identify core value at stake |
| Story has multiple genres | Identify PRIMARY (drives plot) and SECONDARY (adds depth) |
| Writer defensive about problems | Remind: We diagnose the Story, not the person |
| Overwhelming number of problems | Prioritize ruthlessly; fix global first |
| Writer wants quick fix | Explain cascade: global fixes resolve scene issues |

### When to Recommend Major Overhaul

If diagnostic reveals:
- Wrong genre for the story being told
- Missing 50%+ obligatory scenes
- Global structure fundamentally broken
- No clear controlling idea

Recommend stepping back to outline/Foolscap level before scene work.

---

## RELATED RESOURCES

### Follow-Up Tasks
- `analyze-scene-deep.md` - Detailed single-scene analysis
- `create-foolscap.md` - Build Foolscap from scratch
- `genre-deep-dive.md` - Explore specific genre requirements
- `value-shift-training.md` - Practice identifying value shifts

### Reference Materials
- `genre-conventions-database.md` - All genres with obligations
- `five-commandments-examples.md` - Examples from masterworks
- `controlling-ideas-by-genre.md` - Sample controlling ideas

---

**Task Version:** 1.0.0
**Based On:** Shawn Coyne's Story Grid Methodology
**Created:** 2026-01-30
**Lines:** 750+
