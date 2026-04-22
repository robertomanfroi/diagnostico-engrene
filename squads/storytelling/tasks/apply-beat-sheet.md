# Task: Apply Save the Cat Beat Sheet

**Task ID:** apply-beat-sheet
**Version:** 1.0.0
**Agent:** @blake-snyder
**Duration:** 45-90 minutes
**Mode:** Interactive with elicitation
**Output:** Complete Beat Sheet + Story Structure Analysis

---

## Overview

This task guides writers through applying Blake Snyder's complete Save the Cat! methodology to structure a screenplay, novel, or any narrative. Based on Snyder's three books and proven methodology that has structured thousands of successful stories.

> "Structure is not formula. Structure is the skeleton that allows the story to stand." - Blake Snyder

**What This Task Produces:**
1. Complete 15-beat structure with exact timing
2. Genre identification with obligatory scenes
3. Logline with irony and mental picture
4. Six Things That Need Fixing setup
5. Board visualization (40 cards conceptual)
6. Transformation arc mapping

**Sources:**
- "Save the Cat! The Last Book on Screenwriting You'll Ever Need" (2005) - PRIMARY
- "Save the Cat! Goes to the Movies" (2007) - Genre Applications
- "Save the Cat! Strikes Back" (2009) - Advanced Techniques

---

## Prerequisites

Before starting this task, gather:

1. **Story Concept** - Basic idea of what the story is about
2. **Protagonist** - Who is the main character?
3. **Goal** - What does the protagonist want?
4. **Obstacle** - What's preventing them from getting it?
5. **Stakes** - What happens if they fail?
6. **Format** - Screenplay (110 pages), Novel (word count), or other

---

## Phase 1: Logline Creation

### Step 1.1: Extract Core Elements

**Instruction:** Identify the essential story components.

```yaml
story_elements:
  protagonist:
    type: "[TYPE: cop, teacher, student, etc.]"
    adjective: "[DESCRIPTIVE: burnt-out, naive, ambitious, etc.]"
    flaw: "[PRIMARY FLAW to overcome]"

  goal:
    external: "[TANGIBLE goal - what they WANT]"
    internal: "[SPIRITUAL goal - what they NEED]"

  antagonist:
    type: "[TYPE: person, organization, nature, self]"
    adjective: "[DESCRIPTIVE: ruthless, charismatic, etc.]"

  stakes:
    if_fail: "[CONSEQUENCE of failure]"
    ticking_clock: "[TIME PRESSURE if any]"

  setting:
    location: "[WHERE]"
    time: "[WHEN]"
    world: "[ORDINARY vs SPECIAL world contrast]"
```

**Elicitation Questions:**
1. "Who is your protagonist and what one word describes their biggest flaw?"
2. "What tangible thing do they want? What do they truly need?"
3. "Who or what opposes them? Describe in one adjective."
4. "What's at stake if they fail?"

### Step 1.2: Apply Logline Formula

**Template:**
```
"A(n) [ADJECTIVE] [HERO TYPE] must [GOAL] when [SITUATION],
but [COMPLICATION]."
```

**The Four Requirements (Snyder's Rules):**

**1. IRONY (Most Important)**
- The hook that catches interest
- Should provoke "How is THAT going to work?"
- Creates immediate tension

**Test:** Does the logline make someone lean in and say "Tell me more"?

**2. COMPELLING MENTAL PICTURE**
- Reader should "see" the entire movie unfold
- Implies setting and timeframe
- Suggests key scenes

**Test:** Can you visualize the poster and trailer from the logline?

**3. AUDIENCE AND COST**
- Demarcates tone and target audience
- Gives sense of budget/scope
- Buyers know if it can profit

**Test:** Is it clear who this story is for?

**4. KILLER TITLE**
- One-two punch with logline
- "Says what it is" cleverly
- Memorable and evocative

**Test:** Does the title make you want to know more?

### Step 1.3: Logline Examples

**Strong Loglines (Snyder-Approved):**

| Film | Logline | Why It Works |
|------|---------|--------------|
| Die Hard | "A New York cop tries to save his wife and others taken hostage by terrorists during a Christmas party" | Clear hero, clear stakes, ironic setting (Christmas) |
| Pretty Woman | "A businessman falls in love with a hooker he hires to be his date for the weekend" | Strong irony - opposites attract premise |
| Legally Blonde | "A sorority girl enrolls at Harvard Law to win back her ex-boyfriend" | Ironic mismatch, clear goal |
| The Martian | "An astronaut must figure out how to survive alone on Mars when his crew thinks he's dead" | Innocent hero, sudden problem, life-or-death |

**Logline Checklist:**
- [ ] Contains irony that hooks interest
- [ ] Creates compelling mental picture
- [ ] Implies audience and scope
- [ ] Has adjective for hero
- [ ] Has clear, relatable goal
- [ ] Has complication or obstacle
- [ ] Paired with killer title

---

## Phase 2: Genre Identification

### Step 2.1: Determine Your Genre

> "Traditional genre (comedy, drama) tells you the TYPE. My genre tells you HOW the story works." - Snyder

**Genre Decision Tree:**

```
START: What is the core conflict?

Is there a MONSTER and CONFINED SPACE?
├── YES → Monster in the House
└── NO → Continue

Is there a JOURNEY with a PRIZE?
├── YES → Golden Fleece
└── NO → Continue

Is there MAGIC or a WISH granted?
├── YES → Out of the Bottle
└── NO → Continue

Is the hero ORDINARY facing SUDDEN DANGER?
├── YES → Dude with a Problem
└── NO → Continue

Is it about a LIFE TRANSITION or INTERNAL STRUGGLE?
├── YES → Rites of Passage
└── NO → Continue

Is the RELATIONSHIP the main plot?
├── YES → Buddy Love
└── NO → Continue

Is there a MYSTERY about HUMAN NATURE?
├── YES → Whydunit
└── NO → Continue

Is there an UNDERDOG vs. ESTABLISHMENT?
├── YES → Fool Triumphant
└── NO → Continue

Is there GROUP vs. INDIVIDUAL tension?
├── YES → Institutionalized
└── NO → Continue

Is the hero EXTRAORDINARY with a CURSE?
├── YES → Superhero
└── NO → Re-evaluate premise
```

### Step 2.2: Genre Deep Dive

**Complete the profile for your identified genre:**

#### Monster in the House (MITH)
```yaml
genre: Monster in the House
required_elements:
  monster:
    type: "[Supernatural / Human / Nature / Technology]"
    metaphor: "[What evil does the monster represent?]"
    origin: "[How was it created/summoned?]"

  house:
    type: "[Actual house / Ship / Town / Building / etc.]"
    confinement: "[Why can't they escape?]"

  sin:
    transgression: "[What human action invited the monster?]"
    who_sinned: "[Who is responsible?]"
    atonement: "[How will the sin be addressed?]"

key_beats:
  setup: "Establish the 'house' and hint at the 'sin'"
  catalyst: "Monster appears or is awakened"
  fun_and_games: "Cat-and-mouse, survivors picked off"
  midpoint: "Major character death OR monster's true nature revealed"
  all_is_lost: "Hero faces monster alone, seems doomed"
  finale: "Sin acknowledged, monster destroyed"

examples: "Alien, Jaws, Scream, The Ring, Fatal Attraction"
```

#### Golden Fleece
```yaml
genre: Golden Fleece
required_elements:
  road:
    type: "[Physical journey / Time travel / Internal journey]"
    markers: "[Key locations that mark growth]"

  team:
    members: "[List team members]"
    what_they_represent: "[What does each provide that hero lacks?]"

  prize:
    what_is_it: "[The tangible goal]"
    time_pressure: "[Why must it be achieved by a deadline?]"

key_beats:
  setup: "Hero in ordinary world, lacking something"
  catalyst: "Call to the quest"
  fun_and_games: "Road adventures, team bonding"
  midpoint: "Road Apple - something stops the journey cold"
  all_is_lost: "Prize seems lost forever"
  finale: "Prize obtained but hero changed by journey"

examples: "Star Wars, Saving Private Ryan, Ocean's Eleven, Lord of the Rings"
```

#### Out of the Bottle
```yaml
genre: Out of the Bottle
required_elements:
  wish:
    what: "[The wish granted]"
    who_grants_it: "[Magic source]"
    irony: "[How does it go wrong?]"

  spell:
    rules: "[Rules of the magic]"
    limitations: "[What can't the magic do?]"

  lesson:
    what_hero_learns: "[The moral of the wish]"
    how_spell_breaks: "[What breaks the magic?]"

key_beats:
  setup: "Hero dissatisfied with current life"
  catalyst: "Wish is granted"
  fun_and_games: "Enjoying the wish (it seems great at first)"
  midpoint: "Dark side of the wish emerges"
  all_is_lost: "Wish becomes a curse"
  finale: "Hero learns lesson, spell broken"

examples: "Freaky Friday, Bruce Almighty, Liar Liar, What Women Want"
```

#### Dude with a Problem
```yaml
genre: Dude with a Problem
required_elements:
  innocent_hero:
    why_innocent: "[Why are they unprepared for this?]"
    everyperson_quality: "[Why does audience identify?]"

  sudden_event:
    what_happens: "[The inciting incident]"
    no_time: "[Why can't they prepare?]"

  life_or_death:
    stakes: "[What specifically will they lose?]"
    why_matters: "[Why we care]"

key_beats:
  setup: "Ordinary person in ordinary life"
  catalyst: "World explodes - thrust into danger"
  fun_and_games: "Fish out of water surviving"
  midpoint: "First major success OR first major failure"
  all_is_lost: "Seems certain to die"
  finale: "Uses ordinary skills in extraordinary way"

examples: "Die Hard, Home Alone, The Martian, Titanic"
```

#### Rites of Passage
```yaml
genre: Rites of Passage
required_elements:
  life_problem:
    what_is_it: "[Affliction, challenge, or transition]"
    universal_quality: "[Why does everyone relate?]"

  wrong_approach:
    how_hero_handles_it: "[Counterproductive coping]"
    why_it_fails: "[Why this approach makes it worse]"

  acceptance:
    what_hero_accepts: "[The hard truth]"
    how_they_grow: "[The transformation]"

key_beats:
  setup: "Hero facing or denying life problem"
  catalyst: "Problem becomes unavoidable"
  fun_and_games: "Trying wrong approach (seems to work)"
  midpoint: "Wrong approach peaks"
  all_is_lost: "Wrong approach crashes spectacularly"
  finale: "Hero accepts and deals properly"

examples: "10, Ordinary People, 28 Days, Napoleon Dynamite"
```

#### Buddy Love
```yaml
genre: Buddy Love
required_elements:
  incomplete_hero:
    what_missing: "[What does the hero lack?]"
    blind_spot: "[What can't they see about themselves?]"

  counterpart:
    who: "[The buddy/love interest]"
    what_they_have: "[What they provide that hero lacks]"
    why_opposites: "[How are they different?]"

  complication:
    what_threatens: "[What could end the relationship?]"
    internal_external: "[Is it inside or outside the pair?]"

key_beats:
  setup: "Hero incomplete, unaware of what they need"
  catalyst: "Meeting the counterpart"
  fun_and_games: "Getting to know each other (often conflict)"
  midpoint: "First real connection"
  all_is_lost: "Relationship seems destroyed"
  finale: "Reunion after both have changed"

examples: "Lethal Weapon, Rain Man, When Harry Met Sally, E.T."
```

#### Whydunit
```yaml
genre: Whydunit
required_elements:
  detective:
    type: "[Professional / Amateur / Reluctant]"
    flaw: "[What blinds them to the truth?]"

  secret:
    about_what: "[What is the secret really about?]"
    dark_truth: "[What does it reveal about humanity?]"

  dark_turn:
    revelation: "[The shocking discovery]"
    how_it_changes_us: "[How does this change the audience?]"

key_beats:
  setup: "World seems normal, detective enters"
  catalyst: "Mystery presents itself"
  fun_and_games: "Following clues, red herrings"
  midpoint: "Major clue discovered"
  all_is_lost: "Truth seems impossible to find"
  finale: "Dark truth revealed - we are shocked"

examples: "Chinatown, Fargo, Blade Runner, All the President's Men"
```

#### Fool Triumphant
```yaml
genre: Fool Triumphant
required_elements:
  fool:
    innocence: "[What makes them naive/foolish?]"
    hidden_strength: "[What power does their innocence give?]"

  establishment:
    who_they_are: "[The group/system/institution]"
    why_threatened: "[Why does the fool threaten them?]"

  transmutation:
    old_name: "[Who the fool was]"
    new_name: "[Who they become]"
    how_they_change: "[The transformation]"

key_beats:
  setup: "Fool in their innocent world"
  catalyst: "Enters the establishment"
  fun_and_games: "Fool survives through luck and innocence"
  midpoint: "Establishment takes fool seriously"
  all_is_lost: "Establishment seems to crush fool"
  finale: "Fool triumphs through authenticity"

examples: "Forrest Gump, Legally Blonde, Being There, The 40-Year-Old Virgin"
```

#### Institutionalized
```yaml
genre: Institutionalized
required_elements:
  group:
    what_is_it: "[Family / Organization / Institution]"
    rules: "[Explicit and implicit rules]"

  choice:
    conform_or_rebel: "[What must the hero decide?]"
    cost_of_conforming: "[What do they lose?]"
    cost_of_rebelling: "[What do they lose?]"

  sacrifice:
    what_given_up: "[The ultimate sacrifice]"
    for_whom: "[Who benefits?]"

key_beats:
  setup: "Hero enters or is part of the institution"
  catalyst: "Sees something wrong"
  fun_and_games: "Trying to fit in while seeing problems"
  midpoint: "Forced to choose sides"
  all_is_lost: "Rebellion seems to fail"
  finale: "Sacrifice that exposes/changes the institution"

examples: "One Flew Over Cuckoo's Nest, Office Space, Training Day"
```

#### Superhero
```yaml
genre: Superhero
required_elements:
  special_power:
    what_is_it: "[The extraordinary ability]"
    origin: "[How did they get it?]"

  nemesis:
    who: "[The equal and opposite force]"
    connection: "[How are they linked to hero?]"

  curse:
    what_is_it: "[The downside of being special]"
    how_it_isolates: "[Why does it make them lonely?]"

key_beats:
  setup: "Hero discovers/has power, experiences curse"
  catalyst: "Nemesis appears or power tested"
  fun_and_games: "Using powers, dealing with curse"
  midpoint: "Power seems complete"
  all_is_lost: "Nemesis seems to win, curse overwhelms"
  finale: "Accepts both power AND curse to triumph"

examples: "Spider-Man, The Matrix, Gladiator, The Lion King"
```

---

## Phase 3: The 15 Beats

### Step 3.1: Calculate Your Beat Timing

**For Screenplay (110 pages):**
```
Opening Image:     Page 1      (1%)
Theme Stated:      Page 5      (5%)
Set-Up:            Pages 1-10  (1-10%)
Catalyst:          Page 12     (10-12%)
Debate:            Pages 12-25 (12-25%)
Break into Two:    Page 25     (25%)
B Story:           Page 30     (30%)
Fun and Games:     Pages 30-55 (30-55%)
Midpoint:          Page 55     (50%)
Bad Guys Close In: Pages 55-75 (55-75%)
All Is Lost:       Page 75     (75%)
Dark Night:        Pages 75-85 (75-85%)
Break into Three:  Page 85     (85%)
Finale:            Pages 85-110 (85-99%)
Final Image:       Page 110    (100%)
```

**For Novel (Calculate based on word count):**
```python
# Formula: total_words * percentage = beat_position

# Example for 80,000 word novel:
opening_image     = 0          # Word 0
theme_stated      = 4000       # 5% = 80000 * 0.05
catalyst          = 8000       # 10% = 80000 * 0.10
break_into_two    = 20000      # 25% = 80000 * 0.25
b_story           = 24000      # 30% = 80000 * 0.30
midpoint          = 40000      # 50% = 80000 * 0.50
all_is_lost       = 60000      # 75% = 80000 * 0.75
break_into_three  = 68000      # 85% = 80000 * 0.85
final_image       = 80000      # 100%
```

**For Any Format:**
```
[Total Length] x [Beat Percentage] = [Beat Position]
```

### Step 3.2: Complete Each Beat

#### Beat 1: Opening Image (1%)

**Purpose:** "Before" snapshot of protagonist and their flawed world

**Requirements:**
- Single scene
- Sets tone, mood, type, and scope
- Shows protagonist's current state
- Must mirror Final Image to show transformation

**Questions to Answer:**
1. What is the protagonist doing at the start?
2. What flaw or lack is visible?
3. What tone does this establish?
4. What will be the opposite in the Final Image?

**Template:**
```yaml
opening_image:
  scene: "[Describe the opening scene]"
  protagonist_state: "[Emotional/physical state]"
  world_state: "[What's wrong with their world?]"
  tone_established: "[Tone conveyed]"
  mirror_to_final: "[How will Final Image contrast?]"
```

**Film Examples:**
- The Matrix: Blinking command line cursor (technology, mystery)
- Legally Blonde: Elle in pink sorority world (superficial happiness)
- Interstellar: Dusty, dying Earth (desperation)

---

#### Beat 2: Theme Stated (5%)

**Purpose:** Someone states the movie's theme to the protagonist, who doesn't get it yet

**Requirements:**
- Single line or moment
- Delivered by secondary character
- Protagonist dismisses or misunderstands
- Plants seed of what movie is "really about"

**Questions to Answer:**
1. What is your theme in one sentence?
2. Who says it to the protagonist?
3. How does protagonist react?
4. When will they finally understand it?

**Template:**
```yaml
theme_stated:
  theme_in_one_sentence: "[The moral/lesson]"
  who_says_it: "[Character name]"
  exact_line: "[The dialogue or action]"
  protagonist_reaction: "[How they dismiss it]"
  when_understood: "[Beat where they finally get it]"
```

**Film Examples:**
- The Matrix: "You need to unplug" (Neo doesn't understand reality is fake)
- Legally Blonde: "It's not about what you wear" (Elle dismisses this)

---

#### Beat 3: Set-Up (1-10%)

**Purpose:** Establish ordinary world and plant the Six Things That Need Fixing

**Requirements:**
- Multi-scene beat
- Introduce all major A-story characters (or hint at them)
- Establish status quo
- Plant setups that will pay off later

**The Six Things That Need Fixing:**
```yaml
six_things:
  1_character_flaw: "[Primary flaw to overcome]"
  2_basic_need: "[What they need but lack]"
  3_wish: "[What they desire]"
  4_enemies_rivals: "[Who opposes them]"
  5_missing_element: "[What's absent from their life]"
  6_problem: "[Specific problem to solve]"
```

**Plant and Payoff Mapping:**
```yaml
setups_and_payoffs:
  - setup: "[Thing established in Set-Up]"
    payoff: "[How it resolves in Act 3]"

  - setup: "[Another setup]"
    payoff: "[Its payoff]"
```

---

#### Beat 4: Catalyst (10-12%)

**Purpose:** The inciting incident that disrupts the status quo

**Requirements:**
- Single scene beat
- Something happens TO the protagonist
- Life will never be the same
- Clear cause and effect

**Questions to Answer:**
1. What external event disrupts their world?
2. Why can't they ignore it?
3. What choice does this force them to make?

**Template:**
```yaml
catalyst:
  event: "[What happens]"
  who_causes_it: "[External force]"
  why_cant_ignore: "[Stakes if they don't respond]"
  forced_question: "[The question they must answer]"
```

**Film Examples:**
- Hunger Games: Prim's name drawn at the Reaping
- The Matrix: Neo meets Morpheus, offered the red pill
- Die Hard: Terrorists take over Nakatomi Plaza

---

#### Beat 5: Debate (12-25%)

**Purpose:** Hero questions whether to accept the challenge

**Requirements:**
- Multi-scene beat
- Shows reluctance to change
- Last chance to see "old world"
- Presented as a question

**Questions to Answer:**
1. What question does the hero ask themselves?
2. Who do they seek advice from?
3. What almost makes them say no?
4. What finally pushes them to say yes?

**Template:**
```yaml
debate:
  central_question: "[Should I...? / What do I...?]"
  arguments_for: "[Why they might accept]"
  arguments_against: "[Why they hesitate]"
  advisors: "[Who they consult]"
  tipping_point: "[What makes them decide]"
```

---

#### Beat 6: Break into Two (25%)

**Purpose:** Protagonist makes a decisive choice and enters Act Two

**Requirements:**
- Single scene beat
- Clear, active choice by protagonist
- Leaves comfort zone
- Often involves literal change of geography
- Cannot be forced - must be their decision

**Questions to Answer:**
1. What specific action does the hero take?
2. What are they leaving behind?
3. What are they moving toward?
4. How does this demonstrate change?

**Template:**
```yaml
break_into_two:
  the_choice: "[What they decide to do]"
  what_left_behind: "[Old world elements abandoned]"
  new_world_entered: "[Description of upside-down world]"
  physical_movement: "[Literal location change, if any]"
```

**Film Examples:**
- Lord of the Rings: Frodo leaves the Shire
- The Matrix: Neo takes the red pill
- Legally Blonde: Elle applies to Harvard Law

---

#### Beat 7: B Story (30%)

**Purpose:** Introduce the subplot that carries the theme

**Requirements:**
- Single scene beat
- Usually love story, friendship, or mentorship
- New characters often introduced
- Runs parallel to A-story
- B-story character helps hero learn the lesson

**A-Story vs B-Story:**
```yaml
story_contrast:
  a_story:
    focus: "What hero WANTS (external goal)"
    example: "[Your A-story goal]"

  b_story:
    focus: "What hero NEEDS (internal growth)"
    example: "[Your B-story need]"

  connection: "[How B-story teaches A-story lesson]"
```

---

#### Beat 8: Fun and Games (30-55%)

**Purpose:** The "promise of the premise" - what audiences came to see

**Requirements:**
- Multi-scene beat (longest section)
- Delivers on the hook
- The trailer moments, poster images
- Hero either shining OR floundering in new world
- NOT required to be "fun" - means delivering on your premise
- Every scene still needs conflict

**Questions to Answer:**
1. What did your premise promise?
2. What are the trailer-worthy moments?
3. Is the hero succeeding or struggling?
4. How is conflict present in each scene?

**Template:**
```yaml
fun_and_games:
  premise_promise: "[What the concept promised]"
  key_scenes:
    - scene: "[Scene 1]"
      conflict: "[Who vs who]"
      outcome: "[Win/lose/draw]"
    - scene: "[Scene 2]"
      conflict: "[Who vs who]"
      outcome: "[Win/lose/draw]"
  hero_trajectory: "[Upward (false victory) / Downward (false defeat)]"
```

**Film Examples:**
- The Matrix: Neo learns martial arts in The Construct
- Legally Blonde: Elle conquering Harvard, fashion and all
- Home Alone: Kevin defending the house with traps

---

#### Beat 9: Midpoint (50%)

**Purpose:** Stakes raised, game changes

**Requirements:**
- Single scene beat
- EXACT center of the story
- Either FALSE VICTORY or FALSE DEFEAT
- Often introduces a ticking clock
- Connected inversely to All Is Lost

**Midpoint Types:**

**False Victory Midpoint:**
- Things seem to be going great
- Hero achieves apparent success
- But Bad Guys Close In will erode this
- "Things are never as good as they seem at the Midpoint"

**False Defeat Midpoint:**
- Things seem to be going terribly
- Hero hits a low point
- But temporary rally comes
- "Things are never as bad as they seem at the Midpoint"

**Template:**
```yaml
midpoint:
  type: "[False Victory / False Defeat]"
  what_happens: "[The event]"
  stakes_raised_how: "[New stakes introduced]"
  ticking_clock: "[Time pressure added, if any]"
  public_private: "[Does status change publicly?]"
  connection_to_all_is_lost: "[How does it invert?]"
```

**Film Examples:**
- Jurassic Park: T. rex escapes (false defeat - it gets worse before better)
- The Matrix: Neo visits the Oracle (false victory - he thinks he's not The One)

---

#### Beat 10: Bad Guys Close In (55-75%)

**Purpose:** External and internal pressures mount

**Requirements:**
- Multi-scene beat
- Antagonist forces regroup and attack
- Internal doubts, flaws, and jealousies disintegrate the team
- If Midpoint was false victory, things go wrong
- If Midpoint was false defeat, temporary rally then crash
- Things progressively get worse

**Two Types of Pressure:**
```yaml
bad_guys_close_in:
  external_pressure:
    antagonist_actions: "[What the bad guys do]"
    escalating_threats: "[How danger increases]"

  internal_pressure:
    team_conflict: "[Jealousies, doubts, betrayals]"
    hero_flaw_resurface: "[Old flaw comes back]"

  progression:
    beat_1: "[First problem]"
    beat_2: "[Second, worse problem]"
    beat_3: "[Third, worst problem]"
```

---

#### Beat 11: All Is Lost (75%)

**Purpose:** The lowest point of the story

**Requirements:**
- Single scene beat
- Hero hits rock bottom with no hope
- Contains the "Whiff of Death"
- Inverse of the Midpoint
- The old world, old character, old thinking must die

**The Whiff of Death:**

> "In All Is Lost, something DIES. Literally or metaphorically." - Snyder

**Forms of Whiff of Death:**
- Literal death of a character (mentor, friend, ally)
- Death of a dream
- Death of a relationship
- Death of innocence
- Near-death experience
- Death of identity ("Who am I without this?")

**Template:**
```yaml
all_is_lost:
  what_happens: "[The lowest moment]"
  whiff_of_death:
    type: "[Literal / Dream / Relationship / Innocence / Identity]"
    what_dies: "[Specifically what is lost]"
  inverse_of_midpoint: "[If midpoint was up, this is down, and vice versa]"
  no_way_out: "[Why does it seem hopeless?]"
```

**Film Examples:**
- Miss Congeniality: Faces losing her badge and identity
- The Hunger Games: Rue's death
- The Matrix: Morpheus captured, seems doomed

---

#### Beat 12: Dark Night of the Soul (75-85%)

**Purpose:** The darkness before the dawn

**Requirements:**
- Multi-scene beat
- Hero wallows in absolute hopelessness
- Processing the All Is Lost beat
- Unlike Catalyst (happened TO hero), All Is Lost was caused BY hero
- Hero realizes they need to change
- This time, ready to embrace it

**Key Distinction:**
```yaml
dark_night:
  catalyst_comparison:
    catalyst: "Something happened TO the hero"
    all_is_lost: "Hero's own flaw CAUSED this"

  processing:
    questions_hero_asks: "[How did I end up here?]"
    realizations: "[What do they finally see?]"

  preparation:
    old_way_abandoned: "[What they let go of]"
    new_way_glimpsed: "[What they must become]"
```

---

#### Beat 13: Break into Three (85%)

**Purpose:** The epiphany moment - A and B stories combine

**Requirements:**
- Single scene beat
- Hero finds the solution
- Uses what they learned from B-story
- Understands what they must do
- Synthesis of all learning

**Template:**
```yaml
break_into_three:
  epiphany: "[The realization]"
  a_plus_b: "[How A-story goal combines with B-story lesson]"
  solution_found: "[What they now know to do]"
  transformation_visible: "[How they've changed]"
```

---

#### Beat 14: Finale (85-99%)

**Purpose:** The final showdown - hero applies lessons and changes the world

**Requirements:**
- Multi-scene beat
- Hero applies all lessons learned
- Old world replaced by new world
- Bad guys dealt with in ascending order
- Not enough for hero to succeed - they must change the world

**The Five-Point Finale (from Strikes Back):**

```yaml
five_point_finale:
  1_gathering_the_team:
    who: "[Allies assembled]"
    how: "[How they come together]"

  2_executing_the_plan:
    plan: "[Initial strategy]"
    early_success: "[What works at first]"

  3_high_tower_surprise:
    complication: "[What goes wrong at the worst moment]"
    stakes_raised: "[New danger]"

  4_dig_deep_down:
    inner_strength: "[What the hero finds within]"
    transformation_complete: "[How B-story lesson applies]"

  5_execution_of_new_plan:
    new_strategy: "[The adjusted approach]"
    victory: "[How they win]"
    world_changed: "[How the world is different]"
```

---

#### Beat 15: Final Image (100%)

**Purpose:** "After" snapshot showing transformation

**Requirements:**
- Single scene beat
- Mirrors Opening Image
- Shows how much has changed
- Proof that the journey was worth it

**Opening vs Final Image Comparison:**
```yaml
image_comparison:
  opening_image:
    scene: "[Opening scene description]"
    protagonist_state: "[Before state]"
    world_state: "[Before world]"

  final_image:
    scene: "[Final scene description]"
    protagonist_state: "[After state]"
    world_state: "[After world]"

  transformation_shown: "[What changed and how it's visible]"
```

**Film Examples:**
- The Matrix: Opening - cursor blinking; Final - Neo flying
- Legally Blonde: Opening - shopping for engagement ring; Final - law school graduation speech

---

## Phase 4: The Board Method

### Step 4.1: Create Your 40-Card Board

**Board Structure:**
```
Row 1 (Act 1):    [Cards 1-10]   Pages 1-25
Row 2 (Act 2A):   [Cards 11-20]  Pages 25-55
Row 3 (Act 2B):   [Cards 21-30]  Pages 55-85
Row 4 (Act 3):    [Cards 31-40]  Pages 85-110
```

### Step 4.2: Card Template

**Each card must have:**

```yaml
card:
  number: "[1-40]"
  scene_heading: "[INT/EXT - LOCATION - DAY/NIGHT]"
  scene_description: "[Brief description with beginning, middle, end]"
  conflict: "[Who vs. Who - use >< symbol]"
  emotional_change: "[Start emotion → End emotion, use +/-]"
  page_range: "[Estimated pages]"
  color: "[Color code for character/storyline/theme]"
```

### Step 4.3: Color Coding System

```yaml
color_system:
  by_character:
    protagonist: "Blue"
    antagonist: "Red"
    b_story_character: "Pink"
    ally_1: "Green"

  by_storyline:
    a_story: "Blue"
    b_story: "Pink"
    subplot_1: "Yellow"

  by_theme:
    theme_1: "Gold"
    theme_2: "Silver"
```

---

## Phase 5: Validation

### Step 5.1: Beat Sheet Checklist

**Act One (Thesis):**
- [ ] Opening Image shows clear "before" state
- [ ] Theme Stated by ~5%, protagonist doesn't understand
- [ ] Set-Up introduces all major characters
- [ ] Six Things That Need Fixing are planted
- [ ] Catalyst disrupts status quo at ~10-12%
- [ ] Debate shows reluctance to change
- [ ] Break into Two at 25% - clear, active choice

**Act Two (Antithesis):**
- [ ] B Story introduced at ~30%
- [ ] Fun and Games delivers promise of premise (30-55%)
- [ ] Midpoint at exactly 50% - false victory OR false defeat
- [ ] Stakes raised at Midpoint
- [ ] Bad Guys Close In - external AND internal pressure
- [ ] All Is Lost at 75% with Whiff of Death
- [ ] Dark Night of Soul - hero processes and prepares

**Act Three (Synthesis):**
- [ ] Break into Three at 85% - A + B combine
- [ ] Finale uses Five-Point structure
- [ ] Bad guys dealt with in ascending order
- [ ] World is changed, not just hero
- [ ] Final Image mirrors Opening Image

### Step 5.2: Genre Checklist

**Verify your genre elements are present:**
- [ ] All three required elements for your genre
- [ ] Key beats match genre expectations
- [ ] Obligatory scenes are included
- [ ] Genre-specific payoffs delivered

### Step 5.3: Transformation Arc Check

```yaml
transformation_verification:
  hero_at_start:
    flaw: "[Primary flaw]"
    want: "[External goal]"
    need: "[Internal need - unknown to them]"

  hero_at_end:
    flaw_resolved: "[How flaw was overcome]"
    want_achieved: "[Did they get external goal?]"
    need_fulfilled: "[How internal need was met]"

  change_visible: "[Concrete proof of transformation]"
```

---

## Phase 6: Common Mistakes

### Snyder's Top Anti-Patterns

| Mistake | Why It's Wrong | Fix |
|---------|---------------|-----|
| Catalyst too late | Audience gets bored | Move to page 12 |
| Midpoint at wrong percentage | Destroys second act rhythm | Calculate exactly 50% |
| No Whiff of Death | All Is Lost lacks impact | Add death element |
| Break into Two is passive | Hero seems dragged into story | Make it an active choice |
| Final Image doesn't mirror Opening | Transformation unclear | Create explicit contrast |
| Fun and Games doesn't deliver | Broken promise to audience | What did premise promise? |
| B Story carries no theme | Subplot feels disconnected | Link to central theme |
| Double Mumbo Jumbo | Audience suspends disbelief once | Pick one magic system |

---

## Output Template

### Complete Beat Sheet Document

```markdown
# [TITLE] - Save the Cat Beat Sheet

## Logline
[One-sentence logline with irony]

## Genre: [Genre Name]
**Required Elements:**
- [Element 1]: [How it appears]
- [Element 2]: [How it appears]
- [Element 3]: [How it appears]

## The 15 Beats

### ACT ONE - THESIS (Pages 1-25)

**1. Opening Image (p.1)**
[Description]

**2. Theme Stated (p.5)**
[Who says what]

**3. Set-Up (pp.1-10)**
[World establishment + Six Things That Need Fixing]

**4. Catalyst (p.12)**
[Inciting incident]

**5. Debate (pp.12-25)**
[Hero's reluctance]

**6. Break into Two (p.25)**
[The choice]

### ACT TWO - ANTITHESIS (Pages 25-85)

**7. B Story (p.30)**
[Subplot introduction]

**8. Fun and Games (pp.30-55)**
[Promise of premise scenes]

**9. Midpoint (p.55)**
[False Victory/Defeat + Stakes Raised]

**10. Bad Guys Close In (pp.55-75)**
[External and internal pressure]

**11. All Is Lost (p.75)**
[Lowest point + Whiff of Death]

**12. Dark Night of the Soul (pp.75-85)**
[Darkness before dawn]

### ACT THREE - SYNTHESIS (Pages 85-110)

**13. Break into Three (p.85)**
[Epiphany - A+B combine]

**14. Finale (pp.85-110)**
- Gathering the Team:
- Executing the Plan:
- High Tower Surprise:
- Dig Deep Down:
- Execution of New Plan:

**15. Final Image (p.110)**
[Mirror of Opening Image]

## Six Things That Need Fixing
1. [Setup] → [Payoff]
2. [Setup] → [Payoff]
3. [Setup] → [Payoff]
4. [Setup] → [Payoff]
5. [Setup] → [Payoff]
6. [Setup] → [Payoff]

## Transformation Arc
- BEFORE: [Who hero is at start]
- AFTER: [Who hero becomes]
- PROOF: [Visible evidence of change]
```

---

## Sources

### Primary Sources
1. Snyder, Blake. "Save the Cat! The Last Book on Screenwriting You'll Ever Need." Michael Wiese Productions, 2005.
2. Snyder, Blake. "Save the Cat! Goes to the Movies." Michael Wiese Productions, 2007.
3. Snyder, Blake. "Save the Cat! Strikes Back." Save the Cat Press, 2009.

### Secondary Sources
4. Save the Cat! Official Website: https://savethecat.com/
5. StudioBinder Beat Sheet Guide: https://www.studiobinder.com/blog/save-the-cat-beat-sheet/
6. Kindlepreneur Complete Guide: https://kindlepreneur.com/save-the-cat-beat-sheet/

---

**Task Version:** 1.0.0
**Created:** 2026-01-30
**Agent:** @blake-snyder
**Lines:** 850+
**Quality:** Research-backed, based on primary sources
