# Task: Craft Personal Story

**Task ID:** craft-personal-story
**Version:** 1.0.0
**Agent:** @matthew-dicks
**Purpose:** Transform a raw story idea into a compelling personal narrative using Matthew Dicks' proven methodology
**Duration:** 45-90 minutes
**Mode:** Interactive (requires user input at each stage)

---

## Overview

This task guides you through the complete process of crafting a personal story from initial idea to performance-ready narrative. It follows Matthew Dicks' methodology as a 60-time Moth StorySLAM champion, ensuring your story has a clear five-second moment, proper structure, engineered stakes, and passes the Dinner Test.

```
INPUT: Raw story idea, memory, or experience
    |
    v
[STEP 1: Identify the Five-Second Moment]
    → What changed forever? What did you realize?
    |
    v
[STEP 2: Find the Beginning (Opposite of Ending)]
    → Where were you before the transformation?
    |
    v
[STEP 3: Map the Scenes]
    → Location, tone, purpose for each scene
    |
    v
[STEP 4: Apply But/Therefore]
    → Connect scenes with causation, not sequence
    |
    v
[STEP 5: Engineer Stakes]
    → Elephant, Backpack, Breadcrumbs, Hourglass, Crystal Ball
    |
    v
[STEP 6: Craft the Opening]
    → Forward movement, action, immersion
    |
    v
[STEP 7: Add Humor (if appropriate)]
    → Surprise, timing, self-deprecation
    |
    v
[STEP 8: Apply Permissible Lies]
    → Omission, compression, progression for clarity
    |
    v
[STEP 9: Dinner Test Validation]
    → Would you tell it this way to a friend?
    |
    v
OUTPUT: Complete story ready for telling
```

---

## Prerequisites

Before starting, you need:

- [ ] A story idea, memory, or experience you want to develop
- [ ] Willingness to be honest about moments of transformation
- [ ] 45-90 minutes of focused time
- [ ] Optional: A specific context (stage, meeting, presentation, conversation)

---

## Step 1: Identify the Five-Second Moment

**Duration:** 10-15 minutes
**Critical:** This is the heart of your entire story

### The Core Principle

> "All great stories - regardless of length or depth or tone - tell the story of a five-second moment in a person's life. Every great story ever told is essentially about a five-second moment in the life of a human being, and the purpose of the story is to bring that moment to the greatest clarity possible."
> - Matthew Dicks, Storyworthy

### What is a Five-Second Moment?

It's the moment when something fundamentally changed forever. These moments include:

- **Realizations** - "I suddenly understood that..."
- **Decisions** - "In that instant, I decided..."
- **Transformations** - "I was never the same after..."
- **Revelations** - "That's when I saw..."
- **Shifts in belief** - "I stopped believing..."
- **New understanding** - "For the first time, I knew..."

### Elicitation Questions

Answer these questions about your story idea:

```
1. WHAT CHANGED?
   → What was different about you after this experience?
   → What did you believe before that you don't believe now?
   → What did you not know before that you know now?
   → What could you not do before that you can do now?

2. WHEN EXACTLY DID IT CHANGE?
   → Can you pinpoint the exact moment?
   → Where were you standing/sitting?
   → What were you looking at?
   → What triggered the change?

3. HOW LONG WAS THE MOMENT?
   → Was it truly a five-second (or shorter) instant?
   → Or was it gradual? (If gradual, we may need to conflate it)

4. WHY DOES IT MATTER?
   → Why should anyone care about this transformation?
   → What universal truth does it reveal?
   → What will the audience feel?
```

### Output Format

```yaml
five_second_moment:
  description: "[One sentence describing the moment]"
  exact_instant: "[What triggered it, what you saw/heard/felt]"
  transformation:
    before: "[What you believed/felt/were before]"
    after: "[What you believe/feel/are after]"
  universal_truth: "[Why this matters to any human]"
```

### Example

```yaml
five_second_moment:
  description: "The moment I realized my father had always loved me, just not in the way I needed"
  exact_instant: "Seeing his hands shake as he tried to hand me a coffee, and understanding his gruffness was fear, not anger"
  transformation:
    before: "I believed my father was cold and didn't care about me"
    after: "I understood he was terrified of being vulnerable and showing love"
  universal_truth: "We often mistake fear for cruelty in the people who love us most"
```

### Validation Checkpoint

Before proceeding, verify:

- [ ] The moment is SPECIFIC (not vague or general)
- [ ] The moment involves CHANGE (not just an interesting event)
- [ ] The moment is SMALL (five seconds or less, not a gradual process)
- [ ] The moment has UNIVERSAL resonance (others can relate)

If you don't have a clear five-second moment, STOP. Use one of these techniques:
- **Homework for Life** (see task: homework-for-life.md)
- **First/Last/Best/Worst** (see task: first-last-best-worst.md)
- **Crash and Burn** (see task: crash-and-burn.md)

---

## Step 2: Find the Beginning (Opposite of Ending)

**Duration:** 10 minutes

### The Core Principle

> "Simply put, the beginning of the story should be the opposite of the end. Find the opposite of your transformation, revelation, or realization, and this is where your story should start. This is what creates an arc in your story."
> - Matthew Dicks, Storyworthy

### Why This Works

Your story must reflect change over time. Without the opposite beginning, you have:
- A series of events (not a story)
- An anecdote
- A vacation story
- A drinking story

None of these create connection or change minds.

### Finding the Opposite

Based on your five-second moment's transformation:

| If You End As... | You Should Start As... |
|------------------|------------------------|
| Hopeful | Hopeless |
| Found | Lost |
| Confident | Uncertain |
| Fearless | Afraid |
| Accepting | Resistant |
| Connected | Alone |
| Understanding | Confused |
| At peace | In turmoil |
| Trusting | Suspicious |
| Loving | Resentful |

### Elicitation Questions

```
1. WHAT'S THE OPPOSITE STATE?
   → If you ended understanding, when were you most confused?
   → If you ended at peace, when were you most in turmoil?
   → If you ended accepting, when were you most resistant?

2. FIND A SPECIFIC MOMENT
   → Don't just say "I was lost" - where specifically were you?
   → What were you doing?
   → What did that "opposite state" look like in action?

3. HOW FAR BACK?
   → The beginning should be as close in time to the ending as possible
   → But far enough to show the transformation arc
   → Usually the same day or week - rarely months or years apart
```

### Output Format

```yaml
story_arc:
  beginning:
    state: "[Your opposite state]"
    specific_moment: "[Where you were, what you were doing]"
    what_you_believed: "[Your mindset at the start]"
  ending:
    state: "[Your transformed state]"
    five_second_moment: "[The instant of change]"
    what_you_know_now: "[Your new understanding]"
  transformation_statement: "I was once [X], but now I am [Y]"
```

### Example

```yaml
story_arc:
  beginning:
    state: "Resentful and convinced my father didn't love me"
    specific_moment: "Sitting in my car outside his house, dreading another awkward visit"
    what_you_believed: "This man is incapable of showing emotion"
  ending:
    state: "Understanding that his love was hidden behind fear"
    five_second_moment: "His shaking hands trying to hand me coffee"
    what_you_know_now: "Fear often looks like coldness"
  transformation_statement: "I was once certain my father didn't love me, but now I understand he was just afraid to show it"
```

### Validation Checkpoint

- [ ] Beginning state is truly OPPOSITE of ending state
- [ ] Beginning is SPECIFIC (not vague)
- [ ] Beginning shows you in ACTION (not just describing feelings)
- [ ] The arc is CLEAR (audience will see the change)

---

## Step 3: Map the Scenes

**Duration:** 10 minutes

### The Core Principle

> "Storytelling is cinema of the mind. If the audience knows where you are at all times within your story, the movie is running in their minds. Always provide a physical location for every moment of your story."
> - Matthew Dicks, Storyworthy

### Scene Rules

1. **Every moment needs a location** - No floating dialogue or vague settings
2. **Aim for 7 scenes or fewer** - Like phone numbers, 7 is the cognitive limit
3. **Fewer is better** - Some great stories have just one scene
4. **Each scene is a circle** with:
   - **Size** = importance to the story
   - **Color** = emotional tone (warm, cold, tense, light)

### Scene Mapping Template

For each scene in your story:

```yaml
scenes:
  - number: 1
    location: "[Specific physical place]"
    action: "[What happens here]"
    purpose: "[Why this scene exists]"
    tone: "[Emotional color - warm/cold/tense/light/etc.]"
    size: "[Large/Medium/Small - importance]"

  - number: 2
    location: "[Specific physical place]"
    action: "[What happens here]"
    purpose: "[Why this scene exists]"
    tone: "[Emotional color]"
    size: "[Large/Medium/Small]"

  # Continue for each scene...
```

### Example Scene Map

```yaml
scenes:
  - number: 1
    location: "My car, parked outside my father's house, December afternoon"
    action: "Sitting with engine off, hands on wheel, dreading going inside"
    purpose: "Establish the opposition - I don't want to be here, I resent this"
    tone: "Cold, heavy, reluctant"
    size: "Medium"

  - number: 2
    location: "His living room, brown recliner, muted TV playing football"
    action: "Sitting across from him, making small talk, feeling the distance"
    purpose: "Show the pattern - this is how it always is"
    tone: "Awkward, distant"
    size: "Small"

  - number: 3
    location: "His kitchen, standing by the counter"
    action: "He tries to hand me coffee, his hands shake, the cup rattles"
    purpose: "The five-second moment - I see his fear"
    tone: "Shift from cold to warm, revelation"
    size: "Large - this is everything"
```

### Validation Checkpoint

- [ ] Every scene has a SPECIFIC physical location
- [ ] No more than 7 scenes (ideally 3-5)
- [ ] Each scene has a clear PURPOSE
- [ ] The five-second moment scene is clearly identified
- [ ] Tone progression makes sense

---

## Step 4: Apply But/Therefore

**Duration:** 5-10 minutes

### The Core Principle

> "The actual connective tissue in any story should not be 'and.' It should be 'but' or 'therefore.' Stories that connect events with 'and' have no momentum."
> - Matthew Dicks, Storyworthy

### The But/Therefore Test

Go through your scene transitions. Replace every "and then" with "but" or "therefore":

| Bad Transition | Good Transition |
|----------------|-----------------|
| "And then we went to..." | "But when we arrived..." |
| "And then he said..." | "Therefore he told me..." |
| "And then I realized..." | "But suddenly I understood..." |

### Why This Matters

- **"And"** = sequence (boring, no momentum)
- **"But"** = contradiction (direction change, surprise)
- **"Therefore"** = consequence (causation, logic)

This creates a "roller coaster" for your audience, not a flat road.

### Application Template

```yaml
scene_transitions:
  - from_scene: 1
    to_scene: 2
    current_connection: "[How they're currently connected]"
    but_or_therefore: "[Which word fits]"
    revised_connection: "[New connection with but/therefore]"

  - from_scene: 2
    to_scene: 3
    current_connection: "[...]"
    but_or_therefore: "[...]"
    revised_connection: "[...]"
```

### Example

```yaml
scene_transitions:
  - from_scene: 1 (car, dreading)
    to_scene: 2 (living room, small talk)
    current_connection: "And then I went inside"
    but_or_therefore: "therefore"
    revised_connection: "I couldn't sit there forever, therefore I forced myself inside"

  - from_scene: 2 (living room)
    to_scene: 3 (kitchen, shaking hands)
    current_connection: "And then he got up to make coffee"
    but_or_therefore: "but"
    revised_connection: "But when he stood to make coffee, something was different"
```

### Validation Checkpoint

- [ ] Every transition uses "but" or "therefore" (or equivalent)
- [ ] No transitions use "and then"
- [ ] Each transition creates momentum
- [ ] The story feels like it's going somewhere

---

## Step 5: Engineer Stakes

**Duration:** 10-15 minutes

### The Core Principle

> "Stakes are the reason audiences listen and continue to listen to a story."
> - Matthew Dicks, Storyworthy

### The Five Stake-Building Tools

Use at least 2-3 of these techniques in your story:

#### 1. ELEPHANT

> "The Elephant is the thing that everyone in the room can see. It is large and obvious. It is a clear statement of the need, the want, the problem, the peril, or the mystery."

**Requirements:**
- Appears within first 30-60 seconds
- States what the story is about
- Gives audience a reason to listen
- Can "change color" throughout (the problem shifts)

**Application:**
```yaml
elephant:
  statement: "[The clear problem/need/want/mystery]"
  appears_at: "[When in the story]"
  how_stated: "[The exact line or moment]"
  color_changes: "[If/how it shifts]"
```

**Example:**
```yaml
elephant:
  statement: "I haven't had a real conversation with my father in thirty years"
  appears_at: "First 30 seconds"
  how_stated: "As I sit in the car, I realize I can't remember the last time we talked about anything real"
  color_changes: "Shifts from 'he doesn't love me' to 'why can't we connect?' to 'what is he afraid of?'"
```

#### 2. BACKPACK

> "Load up the audience with all the storyteller's hopes and fears in that moment before moving forward."

**Requirements:**
- Comes before a key action
- Shares what you hope will happen
- Shares what you fear will happen
- Most effective when the plan doesn't work

**Application:**
```yaml
backpack:
  moment: "[When in the story]"
  hope: "[What you hope will happen]"
  fear: "[What you fear will happen]"
  outcome: "[What actually happens]"
```

**Example:**
```yaml
backpack:
  moment: "Before getting out of the car"
  hope: "Maybe this time will be different. Maybe we'll actually talk."
  fear: "But it never is. It'll be the same silence, the same TV, the same nothing."
  outcome: "It starts exactly as I feared, but then..."
```

#### 3. BREADCRUMBS

> "Hint at a future event but only reveal enough to keep the audience guessing."

**Requirements:**
- Plant intrigue without answers
- Create wonder about what's coming
- Payoff must be worth the tease

**Application:**
```yaml
breadcrumbs:
  - hint: "[What you plant]"
    payoff: "[Where it pays off]"
    wonder_created: "[What audience will wonder]"
```

**Example:**
```yaml
breadcrumbs:
  - hint: "His hands had always been steady. That's what I remembered most about him."
    payoff: "When they shake handing me the coffee"
    wonder_created: "Why mention his steady hands? Something must happen with them..."
```

#### 4. HOURGLASS

> "The moment to slow things down by adding superfluous detail and summary. Drag out the wait as long as possible."

**Requirements:**
- Use at the moment everyone is waiting for
- Add detail you wouldn't normally include
- Slow down speech, lower volume
- Make them wait

**Application:**
```yaml
hourglass:
  moment: "[The key moment to slow down]"
  details_to_add: "[Superfluous details that build tension]"
  technique: "[How you'll slow it down]"
```

**Example:**
```yaml
hourglass:
  moment: "Him reaching to hand me the coffee"
  details_to_add: |
    The mug was brown with a chip on the handle. It said 'World's Okayest Dad' -
    a gift from my sister years ago. Steam curled up from the surface. He held it
    with both hands, and that's when I noticed...
  technique: "Describe the mug in detail, then his hands, building to the shake"
```

#### 5. CRYSTAL BALL

> "A false prediction made by a storyteller to cause the audience to wonder if the prediction will prove true."

**Requirements:**
- Prediction must seem possible
- Guess must be reasonable
- Must present intriguing possibility

**Application:**
```yaml
crystal_ball:
  prediction: "[Your false prediction]"
  reasoning: "[Why it seems possible]"
  actual_outcome: "[What really happens]"
```

**Example:**
```yaml
crystal_ball:
  prediction: "I knew what would happen. He'd hand me the coffee, say 'Chiefs are up by seven,' and that would be our conversation for the next hour."
  reasoning: "This is exactly what always happens"
  actual_outcome: "But his hands shook, and everything changed"
```

### Stakes Checklist

- [ ] Elephant present in first 30-60 seconds
- [ ] At least one Backpack or Crystal Ball before key action
- [ ] At least one Breadcrumb planted early, paid off later
- [ ] Hourglass used at the key moment
- [ ] Stakes established in first half of story

---

## Step 6: Craft the Opening

**Duration:** 5-10 minutes

### The Core Principle

> "Try to start your story with forward movement whenever possible. Establish yourself as a person who is physically moving through space. Opening with forward movement creates instant momentum in a story."
> - Matthew Dicks, Storyworthy

### What NOT to Do

- DON'T start with: "This is hilarious..." or "You won't believe this..."
- DON'T set expectations
- DON'T start with background or context
- DON'T start sitting or standing still

### What TO Do

Start with movement:
- Walking
- Running
- Driving
- Flying
- Climbing
- Fleeing
- Falling
- Swimming

### Opening Template

```yaml
opening:
  first_line: "[Your opening line with movement]"
  movement_type: "[What kind of movement]"
  location: "[Where you are]"
  direction: "[Where you're going]"
  instant_immersion: "[What puts audience in the scene]"
```

### Example

```yaml
opening:
  first_line: "I'm pulling into my father's driveway on a December afternoon, and I don't want to be here."
  movement_type: "Driving"
  location: "Father's driveway, December"
  direction: "Toward his front door (reluctantly)"
  instant_immersion: "The car, the cold, the reluctance - audience is immediately in the scene"
```

### Alternative Opening (if movement doesn't fit)

If forward movement truly doesn't work, start with:
- Action (any physical action)
- A specific, vivid location
- Dialogue that creates immediate intrigue

But always prefer movement first.

### Validation Checkpoint

- [ ] Opening has physical movement OR strong action
- [ ] Location is immediately clear
- [ ] No expectations are set ("This is crazy...")
- [ ] Audience is IN the scene within first sentence
- [ ] Elephant appears within 30-60 seconds of opening

---

## Step 7: Add Humor (If Appropriate)

**Duration:** 5-10 minutes

### The Core Principle

> "Humor isn't about cracking jokes or trying too hard. It's about finding small, relatable moments that make people smile."
> - Matthew Dicks

### The Laugh Laugh Laugh Cry Technique

If your story ends emotionally or heavy:
1. Make the beginning lighter and funnier
2. Build laughs in the first 60%
3. Pull the rug out for the emotional ending
4. The contrast makes both stronger

### Humor Techniques

#### 1. SURPRISE
The unexpected is the core of humor. Set up one expectation, deliver another.

#### 2. TIMING
Practice pausing before the punch. Emphasize the right words. Pacing matters.

#### 3. SELF-DEPRECATION
Don't take yourself too seriously. Embrace your flaws. It's endearing.

#### 4. RULE OF THREE
Setup, build, surprise:
- "I've tried therapy, meditation, and talking to my houseplants. The plants seem the most helpful."

#### 5. SPECIFICITY
Specific details are funnier than vague ones:
- Not "an old car" but "a 1998 Camry with one working window"

### Application Template

```yaml
humor_opportunities:
  - moment: "[Where in the story]"
    technique: "[Which technique]"
    setup: "[The setup]"
    payoff: "[The laugh]"
```

### Example

```yaml
humor_opportunities:
  - moment: "Opening, in the car"
    technique: "Self-deprecation + specificity"
    setup: "I prepare for visits to my father the way some people prepare for colonoscopies"
    payoff: "Lots of dread, but at least with the colonoscopy you're unconscious for the awkward part"

  - moment: "Living room, small talk"
    technique: "Specificity"
    setup: "We've been talking for twenty minutes"
    payoff: "Topics covered: the weather (twice), the Chiefs, whether the Chiefs can handle the weather, and a detailed review of his new thermostat"
```

### When NOT to Add Humor

- If it feels forced
- If it undermines the emotional core
- If it breaks the Dinner Test (you wouldn't joke about this at dinner)
- If the story is too short to earn it

---

## Step 8: Apply Permissible Lies

**Duration:** 5-10 minutes

### The Core Principle

> "All the lies I tell on stage are never told for my benefit, or for the story's benefit, but for the clarity of the audience."
> - Matthew Dicks, Storyworthy

### The Five Permissible Lies

Review your story and apply these where they help clarity:

#### 1. OMISSION
Cut what's distracting. If someone wasn't essential, pretend they weren't there.

**Ask:** What can I remove without losing the story's meaning?

#### 2. COMPRESSION
Push time and space together. Multiple days become one day.

**Ask:** Can I compress the timeline to heighten drama?

#### 3. ASSUMPTION
Add specific details that must be true even if you don't remember exactly.

**Ask:** What reasonable assumptions make this clearer?

#### 4. PROGRESSION
Change the order if real life didn't follow good narrative structure.

**Ask:** Would a different order be more emotionally satisfying?

#### 5. CONFLATION
Push gradual change into a single moment.

**Ask:** Can I combine multiple realizations into one five-second moment?

### Application Template

```yaml
permissible_lies:
  omission:
    - what_cut: "[What you're removing]"
      why: "[Why it doesn't serve the story]"

  compression:
    - original_timeline: "[What really happened over what time]"
      compressed_to: "[What you'll say happened]"
      benefit: "[Why this is clearer]"

  assumption:
    - detail: "[Specific detail you're adding]"
      reasoning: "[Why it's reasonable to assume]"

  progression:
    - original_order: "[Real order]"
      new_order: "[Story order]"
      emotional_benefit: "[Why this works better]"

  conflation:
    - gradual_process: "[What really happened over time]"
      single_moment: "[How you'll present it]"
```

### Critical Rule

**Only lie for the audience's benefit, never for personal gain.**

NOT okay:
- Making up things that didn't happen
- Making yourself look better
- Inventing drama that wasn't there

---

## Step 9: Dinner Test Validation

**Duration:** 5 minutes

### The Core Principle

> "Is the story that you craft for the stage, the boardroom, the sales conference, or the Sunday sermon similar to the story you would tell a friend at dinner? The performance version and the casual version should be 'kissing cousins.'"
> - Matthew Dicks, Storyworthy

### The Dinner Test Checklist

Read through your story and check:

#### Language & Delivery
- [ ] No purple prose ("purple pansies were particularly pleasant...")
- [ ] No weird hand gestures you wouldn't do at dinner
- [ ] No theatrical affectations
- [ ] No overly poetic language
- [ ] No invented dialogue that sounds rehearsed

#### Authenticity
- [ ] You would actually tell it this way to a friend
- [ ] It sounds like YOU, not a performance
- [ ] The emotion feels real, not manufactured
- [ ] You're not trying too hard

#### Structure
- [ ] It's not over-engineered
- [ ] The humor is natural, not forced
- [ ] The transitions flow naturally
- [ ] The ending lands without being preachy

### Final Validation

Answer these questions:

```
1. Would you tell this story at dinner with close friends?
   → Yes / No / With modifications

2. Would you be embarrassed by how "performance-y" it sounds?
   → No = good / Yes = revise

3. Does it sound like you or like "a storyteller"?
   → Like you = good / Like a storyteller = revise

4. Is there any moment where you'd cringe telling it casually?
   → No cringe moments = good / Yes = cut those parts
```

### If You Fail the Dinner Test

Simplify:
- Cut theatrical elements
- Remove forced humor
- Speak it out loud as if to a friend
- Record yourself telling it casually, then transcribe

---

## Step 10: Final Assembly

**Duration:** 5-10 minutes

### Complete Story Template

```yaml
story:
  title: "[Working title]"
  duration: "[Estimated time to tell]"

  five_second_moment:
    description: "[One sentence]"
    universal_truth: "[Why it matters]"

  arc:
    beginning_state: "[Opposite of ending]"
    ending_state: "[Transformed state]"
    transformation: "I was once [X], but now I am [Y]"

  opening_line: "[First sentence with movement]"

  scenes:
    - number: 1
      location: "[Where]"
      key_action: "[What happens]"

    # ... continue for each scene

  stakes_used:
    - elephant: "[Statement]"
    - backpack: "[Hopes/fears]"
    - breadcrumbs: "[What's planted]"
    - hourglass: "[Key moment slowed]"
    - crystal_ball: "[False prediction]"

  humor_moments:
    - "[Where and what]"

  permissible_lies_applied:
    - "[What and why]"

  dinner_test: "PASS / CONDITIONAL / REVISE"
```

### Story Draft

Write out your complete story using all elements above. Include:

1. **Opening** (with movement)
2. **Elephant** (within 30-60 seconds)
3. **Scene progression** (with But/Therefore)
4. **Stakes** (throughout first half)
5. **Hourglass** (at key moment)
6. **Five-second moment** (the transformation)
7. **Landing** (the new understanding)

---

## Output: Your Complete Story

### Example Output

```
TITLE: The Shaking Hands

DURATION: 5-6 minutes

OPENING:
I'm pulling into my father's driveway on a December afternoon, and I don't want to be here.

[ELEPHANT - stated immediately]
I haven't had a real conversation with this man in thirty years. Our relationship consists entirely of weather reports, Chiefs scores, and long silences that we've both gotten comfortable with.

[BACKPACK - before going in]
I sit in the car, hoping maybe this time will be different. Maybe we'll actually talk. But it never is. It'll be the same silence, the same TV, the same nothing.

[BUT - transition to scene 2]
But I can't sit here forever, so I force myself out of the car and toward his front door.

[BREADCRUMB - planted early]
The thing I remember most about my father's hands is how steady they were. When I was a kid, he could hold a nail perfectly still while hammering it in. Never missed. Those steady hands.

[SCENE 2 - living room]
And there he is in his brown recliner, TV on mute but still showing football, already asking me about the weather as I'm taking off my coat.

[HUMOR - specificity]
Twenty minutes later, we've covered all the major topics: the weather (twice), the Chiefs, whether the Chiefs can handle the weather, and a detailed review of his new thermostat.

[BUT - transition to scene 3]
But then he stands up and says he's going to make coffee, and something feels different.

[HOURGLASS - slowing down the key moment]
I follow him to the kitchen. He pulls down a mug from the cabinet - brown, with a chip on the handle. It says "World's Okayest Dad" - a gift from my sister years ago. Steam curls up from the Folgers. He holds the mug with both hands and turns to give it to me.

[FIVE-SECOND MOMENT]
That's when I see it. His hands are shaking. The mug rattles against the saucer. My father, whose hands could hold a nail perfectly still, can barely hold a cup of coffee.

And in that moment, I understand. The gruffness. The distance. The thirty years of weather reports instead of feelings. It wasn't coldness. It was fear. He's terrified. Terrified of saying the wrong thing. Terrified of being vulnerable. Terrified that if he lets me see him, really see him, I won't like what I find.

[LANDING - transformation]
I take the coffee from his shaking hands and I say something I've never said before: "Thanks, Dad."

He nods. We don't talk about it. We probably never will. But I understand now that love doesn't always look like we expect it to. Sometimes it looks like thirty years of weather reports and a cup of Folgers from shaking hands.

I was once certain my father didn't love me. Now I understand he was just afraid to show it.
```

---

## Quality Checklist: Final Review

Before considering your story complete:

### Structure
- [ ] Five-second moment is clear and specific
- [ ] Beginning is opposite of ending
- [ ] No more than 7 scenes
- [ ] Every scene has a physical location
- [ ] But/Therefore connects all scenes (no "and then")

### Stakes
- [ ] Elephant appears in first 30-60 seconds
- [ ] At least 2-3 stake techniques used
- [ ] Stakes established in first half
- [ ] Hourglass used at key moment

### Authenticity
- [ ] Passes the Dinner Test
- [ ] Sounds like you, not a performer
- [ ] Emotion is real, not manufactured
- [ ] Humor is natural (if used)

### Impact
- [ ] Universal truth is clear
- [ ] Audience will feel something
- [ ] Transformation is earned
- [ ] Landing resonates

---

## Practice Recommendations

1. **Tell it out loud** - Stories are meant to be spoken
2. **Time yourself** - Aim for 5-7 minutes for most stories
3. **Record and review** - Listen for false notes
4. **Test on friends** - Use the Dinner Test literally
5. **Iterate** - Great stories are revised many times

---

**Task Version:** 1.0.0
**Created:** 2026-01-30
**Methodology:** Matthew Dicks, "Storyworthy" (2018)
**Author:** AIOX Squad Architect

---

## Research Sources

This task is built on primary research from:

1. **Storyworthy** by Matthew Dicks (2018) - New World Library
2. **Matthew Dicks Official Website** - matthewdicks.com
3. **Storyworthy Training Programs** - storyworthymd.com
4. **Lenny's Podcast** - "How to Tell Better Stories | Matthew Dicks"
5. **The Knowledge Project Ep. #202** - "Matthew Dicks: The Storytelling Expert"
6. **The Moth** - Official archive of Matthew Dicks' stories
7. **Multiple book summaries and analyses** validating the methodology

All techniques, principles, and processes are directly traceable to Matthew Dicks' documented work.
