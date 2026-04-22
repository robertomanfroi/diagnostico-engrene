# Task: Create Pitch Using STRONG Method

**Task ID:** create-pitch
**Version:** 1.0.0
**Agent:** @oren-klaff
**Duration:** 60-120 minutes
**Mode:** Interactive with elicitation
**Output:** Complete Pitch Structure + Frame Strategy + Hot Cognition Stack

---

## Overview

This task guides entrepreneurs and salespeople through creating a compelling pitch that closes deals using Oren Klaff's complete STRONG methodology. Based on Klaff's research in neuroeconomics and proven track record of raising over $400 million.

> "Creating and presenting a great pitch isn't an art—it's a simple science, applying the latest findings in the field of neuroeconomics." - Oren Klaff

**What This Task Produces:**
1. Complete STRONG-method pitch structure (20 minutes max)
2. Frame control strategy with counter-frames
3. Hot cognition stack for emotional engagement
4. Status dynamics analysis and positioning
5. Croc brain optimized messaging
6. Neediness elimination checklist
7. Hookpoint and closing strategy

**Sources:**
- "Pitch Anything: An Innovative Method for Presenting, Persuading, and Winning the Deal" (2011) - PRIMARY
- "Flip the Script: Getting People to Think Your Idea Is Their Idea" (2019) - PRIMARY
- Oren Klaff interviews and case studies - SECONDARY

---

## Prerequisites

Before starting this task, gather:

1. **Your Offer** - What exactly are you pitching?
2. **Target Audience** - Who are you pitching to?
3. **Your Background** - What gives you credibility?
4. **The Ask** - What do you want them to do?
5. **Competition** - What alternatives do they have?
6. **Unique Value** - Why you over alternatives?

---

## Phase 1: Croc Brain Analysis

### Step 1.1: Understand the Three-Brain Model

**Instruction:** Before pitching, understand how decisions are made.

> "The fact that you are pitching your idea from the neocortex but it is being received by the other person's croc brain is a serious problem."

**The Three Brains:**

```yaml
brain_model:
  croc_brain:
    name: "Crocodile Brain (Primitive)"
    function: "Initial filter for ALL incoming messages"
    focus: "Survival - is this dangerous? Can I ignore it?"
    capacity: "Limited - devoted primarily to staying alive"
    decision_style: "Fast, emotional, gut-level"
    your_challenge: "Your message must pass THIS filter first"

  midbrain:
    name: "Middle Brain"
    function: "Determines meaning of things and social situations"
    role: "Context and social dynamics"

  neocortex:
    name: "Neocortex"
    function: "Problem-solving, complex thought, reason"
    capacity: "High - analytical and logical"
    warning: "Does NOT make buying decisions"
    common_mistake: "Pitching TO neocortex when croc brain decides"
```

### Step 1.2: Map Your Message to Croc Brain Needs

**The Croc Brain Only Cares About:**

1. **Is it dangerous?** - Avoid triggering threat response
2. **Is it new/interesting?** - Novelty captures attention
3. **Should I pay attention?** - Must earn brain resources

**Elicitation Questions:**
1. "What about your pitch might seem threatening or risky to them?"
2. "What's genuinely novel about your offer?"
3. "Why should their primitive brain care?"

**Template:**

```yaml
croc_brain_analysis:
  potential_threats:
    - threat: "[What might trigger fear/threat response]"
      mitigation: "[How to present it safely]"
    - threat: "[Another potential threat]"
      mitigation: "[Mitigation strategy]"

  novelty_factors:
    - "[What's new about your offer]"
    - "[What's unexpected]"
    - "[What breaks their pattern]"

  attention_hooks:
    - "[Why their primitive brain should care]"
    - "[Survival/gain connection]"
    - "[What's at stake for THEM]"
```

### Step 1.3: Hot vs Cold Cognition Strategy

> "To an overwhelming degree, people make decisions based on hot cognitions—emotions—rather than cold cognitions—rational analyses. We use facts and data to justify our decisions after we've made them."

**Template:**

```yaml
cognition_strategy:
  hot_cognition_triggers:
    desire: "[What will they WANT]"
    excitement: "[What will excite them]"
    fear_of_missing: "[What might they lose]"
    status: "[How does this elevate their status]"

  cold_cognition_handling:
    when_they_go_analytical: "Deploy intrigue frame (see Phase 4)"
    data_requests: "Handle AFTER emotional engagement"
    spreadsheet_demands: "Redirect to narrative"
    your_response: "Details we can review later, but first let me show you..."

  key_insight: |
    "You can trigger a hot cognition instantly,
    but cold cognition can take hours or days."
    Win the emotional decision FIRST.
```

---

## Phase 2: Status Dynamics Setup

### Step 2.1: Assess Status Landscape

> "Within seconds, we each need to decide: who in this room is the dominant alpha? And if it turns out that someone else is the dominant alpha and we are the beta, can we switch out of the beta position and take the alpha?"

**Global vs Situational Status:**

```yaml
status_assessment:
  global_status:
    definition: "Professional position, wealth, reputation"
    your_global_status: "[Your professional standing]"
    their_global_status: "[Their professional standing]"
    gap: "[Who has higher global status]"
    note: "Cannot change this moment-to-moment"

  situational_status:
    definition: "Status during THIS encounter - fluid, changeable"
    opportunity: "Lower global status person CAN have higher situational status"
    your_goal: "Seize situational status through Local Star Power"
```

### Step 2.2: Identify Beta Traps

> "Beta traps are small ways that your target sets the rules. Our croc brains recognize that the one who sets the rules is the one in command."

**Common Beta Traps to Avoid:**

```yaml
beta_traps:
  physical_control:
    examples:
      - "Sign here, sit there, wear this badge"
      - "Wait in the lobby"
      - "The conference room is this way"
    your_response: "Politely ignore, don't accept subordinate position"

  time_control:
    examples:
      - "I have 15 minutes"
      - "Can you make it quick?"
      - "I'm very busy today"
    your_response: "Set YOUR time constraint first"

  presentation_control:
    examples:
      - "You can start your presentation now"
      - "Walk us through your deck"
      - "What do you have for us?"
    your_response: "Reframe: 'Before I dive in, I'd like to understand...'"

  approval_seeking:
    examples:
      - Waiting for their nod to continue
      - Asking "Does that make sense?"
      - Checking for permission
    your_response: "State, don't ask. Move forward confidently."
```

### Step 2.3: Establish Local Star Power

> "To be the star of the show, for the duration of your meeting, you must be more knowledgeable, competent, and skillful than the others in the room in some specific area."

**Elicitation Questions:**
1. "What domain are you THE expert in?"
2. "What do you know that they cannot challenge?"
3. "What's your superpower they need?"

**Template:**

```yaml
local_star_power:
  your_domain_expertise:
    area: "[Specific area where you are the undisputed expert]"
    credentials: "[What makes you the expert]"
    knowledge_they_need: "[What you know that they don't]"

  how_to_establish:
    step_1: "After taking power, immediately redirect discussion to YOUR domain"
    step_2: "Demonstrate expertise without explaining or justifying"
    step_3: "Make them realize they need YOUR knowledge"

  flash_roll_script:
    duration: "90 seconds"
    content: "[Technical mastery demonstration - speak FASTER here]"
    purpose: "Prove expertise linguistically"
    example: |
      "In the [domain], we see three critical factors: [factor 1] which impacts
      [consequence], [factor 2] driving [result], and the often-overlooked
      [factor 3] that determines [outcome]. The intersection of these creates
      [your unique insight]. Most people miss this because [reason]..."

  warning: "Local Star Power DISAPPEARS when you leave the meeting - establish it early"
```

### Step 2.4: Status Tip-Off (From Flip the Script)

> "Job #1 in flipping the script is to get the other person to take you seriously. You do that by giving them a status tip-off that you're on the same level as them."

**Template:**

```yaml
status_tip_off:
  definition: "Brief story or phrase only known by people who know the industry well"

  how_to_find:
    method: "Interview 3 people at the same level as your target"
    question: "What would they say to each other, to catch up on business, peer-to-peer?"

  your_status_tip_off:
    phrase: "[Industry insider language/reference]"
    context: "[When to drop it naturally]"
    effect: "They recognize you as peer, not outsider"

  examples:
    investment: "We're seeing the Series B compression everyone predicted..."
    real_estate: "With cap rates where they are post-rate hike..."
    tech: "The technical debt on legacy systems is creating M&A opportunities..."
```

---

## Phase 3: Frame Control Strategy

### Step 3.1: Understand Frames

> "A frame is a perspective, a point of view, or a narrative perspective. Every pitch meeting is a collision of frames. The stronger frame always absorbs the weaker frame."

**Frame Fundamentals:**

```yaml
frame_principles:
  definition: "Frame = lens through which reality is perceived"

  collision_rule: "When frames collide, ONE wins - the stronger absorbs the weaker"

  control_rule: "Whoever controls the frame controls the conversation"

  key_insight: |
    "If you have to explain your authority, power, position, leverage,
    or advantage, you do not hold the stronger frame."

  your_goal: "Set YOUR frame before they set theirs"
```

### Step 3.2: Anticipate Opposing Frames

**The Three Frames You WILL Encounter:**

#### Power Frame Analysis

```yaml
power_frame:
  recognition:
    - Big ego rooted in their position/authority
    - Expects YOU to adopt their worldview
    - Uses environment to establish dominance
    - Interrupts to show control
    - Name-drops or credential-flashes

  your_counter: "Power-Busting Frame"

  strategy:
    rule_1: "Do NOT react to their power display"
    rule_2: "Do nothing that strengthens their frame"
    rule_3: "Look for opportunity for small denial or defiance"
    rule_4: "Defiance + Humor = Frame Control"

  your_power_bust:
    trigger: "[What they might do to assert power]"
    response: "[Your defiant + humorous response]"
    example:
      their_move: "Checking phone during your intro"
      your_response: "I see you're popular. Should I wait for that or
                      would you rather I show you the thing that made
                      [impressive company] call ME three times last week?"
```

#### Time Frame Analysis

```yaml
time_frame:
  recognition:
    - "I only have 15 minutes"
    - Checking watch repeatedly
    - "Can you speed this up?"
    - Making you feel rushed

  your_counter: "Time-Constraining Frame"

  strategy:
    rule_1: "Never run long - shows weakness and neediness"
    rule_2: "Set YOUR time constraint first"
    rule_3: "When attention fades, don't push - bounce"
    rule_4: "Being prepared to leave signals strength"

  your_time_constraint:
    opening: "[Your pre-emptive time frame statement]"
    example: "I have a hard stop in 25 minutes, so let's make sure
              we cover what matters. If we need more time, my assistant
              can find a slot next week."

    mid_pitch_check: "We're 10 minutes in. Are you getting what you need,
                      or should we pivot?"
```

#### Analyst Frame Analysis

```yaml
analyst_frame:
  recognition:
    - Focus on data and spreadsheets
    - "What are the unit economics?"
    - "Show me the numbers"
    - Cold, calculating demeanor
    - Common in: Engineers, Financial Analysts, CPAs

  your_counter: "Intrigue Frame"

  danger: |
    "This frame will kill your pitch."
    When they go analytical, they shift to cold cognition.
    Cold cognition does NOT make buying decisions.

  strategy:
    rule_1: "Never engage in analysis DURING the pitch"
    rule_2: "Humans cannot have hot AND cold cognition simultaneously"
    rule_3: "Use intrigue story to hijack higher cognitive function"
    rule_4: "Redirect: 'Technical details later, but first...'"

  your_intrigue_story:
    setup: "[Begin a compelling narrative]"
    tension: "[Add conflict and stakes]"
    cliff_hanger: "[Do NOT finish - leave them wanting]"

    man_in_jungle_formula:
      step_1: "Put a man in the jungle"
      step_2: "Have beasts attack him"
      step_3: "Will he get to safety?"
      key_insight: "It's not what happens TO you that's interesting,
                    it's what you DO about the situation"
```

### Step 3.3: Build Your Frame Stack

> "Klaff doesn't stop at a single frame. He teaches frame stacking—layering frames to build momentum, intrigue, and control."

**Template:**

```yaml
frame_stack:
  order: "Intrigue → Power → Prize → Time"

  layer_1_intrigue:
    story: "[Your intrigue story that hooks attention]"
    cliff_hanger: "[Unresolved tension point]"
    purpose: "Capture attention, bypass cold cognition"

  layer_2_power:
    your_authority: "[Why you are the expert]"
    demonstration: "[How you show, not tell]"
    defiance: "[Small challenge to their frame if needed]"
    purpose: "Establish you as alpha in this domain"

  layer_3_prize:
    positioning: "[Why YOU are the prize]"
    scarcity: "[Why this opportunity is limited]"
    qualification: "[What THEY must prove to you]"
    purpose: "Flip dynamic - they chase you"

  layer_4_time:
    constraint: "[Legitimate urgency]"
    deadline: "[Real timeline pressure]"
    consequence: "[What happens if they wait]"
    purpose: "Force decision, prevent cold analysis"
```

---

## Phase 4: The STRONG Method Pitch Structure

### Step 4.1: S - Set the Frame (Minutes 1-5)

> "Frame control begins before the pitch even starts. A frame is the instrument you use to package your information, authority, power, strength, and status."

**Objectives:**
- Establish YOUR frame immediately
- Defeat opposing frames
- Set time constraint
- Demonstrate Local Star Power

**Template:**

```yaml
set_the_frame:
  opening_statement:
    time_constraint: "[Your time limit statement]"
    frame_setter: "[Statement that establishes your perspective]"
    authority_signal: "[Brief credential without explanation]"

  script_template: |
    "I have [time] before my next meeting, so let's dive right in.

    [Frame setter - the lens you want them to see through]

    Most people in [their situation] think [common belief].
    What we've discovered after [your experience] is that [your insight]."

  example:
    context: "Pitching a startup to VCs"
    script: |
      "I have about 25 minutes before my call with [name-drop if real].
      So let me get right to it.

      Most founders come in here talking about their product.
      I'm not going to do that.

      After raising [amount] and working with [impressive names],
      we've learned that the only thing that matters is
      [unique insight that positions you as expert]."

  power_bust_ready:
    if_they_try: "[Anticipated power move]"
    your_response: "[Defiant + humorous counter]"
```

### Step 4.2: T - Tell the Story (Minutes 5-8)

> "Tell the story, a narrative—paint the picture out of facts and figures by putting in human relationships and time frames."

**Objectives:**
- Present your Big Idea in narrative form
- Engage emotions, not analytics
- Create tension and curiosity

**The Big Idea Framework:**

```yaml
big_idea:
  formula: "[For WHO] + [doing WHAT] + [that creates RESULT]"

  your_big_idea: "[Complete Big Idea statement]"

  context_setup:
    market_situation: "[What's happening in the market/world]"
    forces_at_play: "[Three economic/social/tech forces creating opportunity]"
    timing: "[Why NOW is the moment]"

  example_format: |
    "Three forces are converging right now:
    1. [Force 1 - external trend]
    2. [Force 2 - market shift]
    3. [Force 3 - behavioral change]

    This creates a [size] opportunity for whoever [action].
    We've built the [solution] that [unique capability]."
```

**Narrative Structure:**

```yaml
story_structure:
  setup:
    world_as_it_is: "[Current state - the problem]"
    who_is_affected: "[Real people with real pain]"
    what_they_tried: "[Failed solutions]"

  tension:
    conflict: "[What's at stake]"
    urgency: "[Why it must be solved now]"
    consequences: "[What happens if unsolved]"

  your_entry:
    discovery: "[How you found the solution]"
    struggle: "[Challenges you overcame]"
    proof: "[Evidence it works]"

  key_principle: |
    "With the human brain, 20 minutes is all you've got.
    If the story's boring or not in narrative format,
    that brain checks out."
```

### Step 4.3: R - Reveal the Intrigue (Minutes 8-12)

> "The Intrigue Frame is designed to capture and hold your audience's attention by leveraging curiosity and suspense."

**Objectives:**
- Maintain curiosity
- Create information gap
- Deploy Man in the Jungle story

**Template:**

```yaml
intrigue_revelation:
  curiosity_driver: |
    "You can drive curiosity from an information gap—
    the difference between what you know and what you want to know."

  intrigue_story:
    man_in_jungle:
      protagonist: "[You or relatable figure]"
      jungle: "[Dangerous situation/environment]"
      beasts: "[Threats/challenges]"
      suspense: "[Unresolved - will they survive?]"

    your_story:
      setup: "[Set the scene - who, where, when]"
      crisis: "[The dangerous moment]"
      action: "[What you DID about it - not what happened TO you]"
      cliff_hanger: "[Don't resolve yet - leave wanting more]"

  tension_loop:
    push: "Establish boundaries, create tension"
    pull: "Offer value, relieve tension"
    rhythm: "Alternate to keep engagement"

  example_structure: |
    "Let me tell you about what happened with [client/deal].

    [Setup - they were in a situation]
    [Crisis - things went wrong]
    [What we did - your action]

    Now, what happened next... actually, let me come back to that.
    First, let me show you [pivot to next point]."

  warning: |
    "When the prospect knows enough to understand your big idea,
    curiosity ends and your pitch is effectively over."
```

### Step 4.4: O - Offer the Prize (Minutes 12-15)

> "Prizing is the sum of the actions you take to get your target to understand that he is a commodity and you are the prize."

**Objectives:**
- Position yourself as the prize
- Make them qualify to you
- Flip the dynamic

**Template:**

```yaml
offer_the_prize:
  core_principle: |
    "Who is the prize, or who is chasing whom, is one of the
    underlying social dynamics that influences most meetings."

  prize_positioning:
    you_are_prize_because:
      - "[Unique capability 1]"
      - "[Unique capability 2]"
      - "[Scarcity factor]"

    money_is_commodity_because:
      - "Everyone has money"
      - "Money can't execute without you"
      - "Your opportunity is unique, their capital isn't"

  reframe_their_questions:
    their_question: "Why should we invest in you?"
    your_reframe: "That's a fair question. But I'm also evaluating
                   partners carefully. What would make you the right
                   partner for this opportunity?"

  make_them_qualify:
    questions_to_ask_them:
      - "What experience do you have in this space?"
      - "How have you helped other companies like ours?"
      - "What do you bring beyond capital?"

    effect: "Shifts dynamic - they prove worthiness to you"

  withdrawal_technique:
    when_to_use: "At crucial moment when they expect you to push"
    script: |
      "Look, I want to be honest with you.
      This might not be the right opportunity for everyone.
      If it doesn't feel like a fit, that's completely fine.
      We're being selective about who we work with."

  example_script: |
    "[After presenting value]

    Now, we've had interest from [name-drop if real].
    But I'm not just looking for money or customers.
    I'm looking for partners who can add [specific value].

    Before I continue, I'd like to understand:
    What would make you the right partner for this?"
```

### Step 4.5: N - Nail the Hookpoint (Minutes 15-17)

> "The hookpoint is the place in the presentation where your listeners become emotionally engaged."

**Objectives:**
- Create emotional engagement moment
- Deploy hot cognition stack
- Achieve visceral "I want this" reaction

**Template:**

```yaml
nail_hookpoint:
  definition: "The moment of emotional engagement - they FEEL they want it"

  intrigue_ping:
    definition: "Short, provocative piece of information that arouses curiosity"
    your_ping: "[Unexpected fact/insight that makes them lean in]"

  hot_cognition_stack:
    deploy_order:
      1:
        frame: "Intrigue"
        action: "Your unfinished story from earlier"
        effect: "Curiosity peak"

      2:
        frame: "Prize"
        action: "Reinforce your value, their commodity"
        effect: "Desire to win you"

      3:
        frame: "Time"
        action: "Introduce legitimate urgency"
        effect: "Fear of missing out"

      4:
        frame: "Moral Authority"
        action: "Make them justify their worthiness"
        effect: "They sell themselves"

  attention_cocktail:
    ingredients: "Novelty + Tension"
    how_it_works: "Work together in feedback loop for ~20 minutes"
    warning: "After 20 minutes, they get out of balance and stop working"

  hookpoint_script:
    resolve_intrigue: "[Finish your Man in the Jungle story now]"
    connect_to_them: "[How this relates to THEIR situation]"
    emotional_peak: "[The 'aha' moment you've built toward]"

  example: |
    "Remember that story about [situation]?

    Here's what happened: [resolution that demonstrates your value]

    Now, your situation is [similar/different in key way].
    The same [principle] applies.

    [Pause - let it land]

    The question is: are you going to [miss this / seize this]?"
```

### Step 4.6: G - Get the Decision (Minutes 17-20)

> "When you are the prize, the dynamics of money come alive. Money seeks out those who are prize-framed."

**Objectives:**
- Ask for the decision directly
- Maintain prize frame
- Handle without neediness

**Template:**

```yaml
get_decision:
  pre_close_check:
    your_question: "Based on what you've seen, does this feel like
                    something worth exploring further?"
    their_answer: "[Gauge temperature]"
    adjustment: "[Pivot based on response]"

  direct_ask:
    script_options:
      confident: "So, are you in?"

      collaborative: "What would it take to move forward together?"

      prize_framed: "I'm meeting with [others] this week.
                     If this is something you want to be part of,
                     I'll need to know by [deadline]."

      withdrawal: "I can see this might not be the right timing for you.
                   Should we reconnect in [timeframe]?"

  handling_responses:
    yes:
      action: "Great. Let's discuss next steps."
      avoid: "Over-thanking, showing relief, celebrating prematurely"
      maintain: "Prize frame - this is expected, not a gift"

    need_to_think:
      diagnosis: "Cold cognition taking over - danger zone"
      response: "I understand. What specifically do you need to think about?"
      reframe: "In my experience, the decision often comes down to [hot cognition factor].
                How do you feel about that aspect?"

    objection:
      approach: "Don't argue. Use prize frame."
      response: "That's a fair concern. And to be honest, this might not be
                 the right fit. [Pause] But let me ask you this: [reframe question]"

    no:
      approach: "Accept gracefully. Maintain status."
      response: "I appreciate the directness. If circumstances change,
                 you know where to find me."
      avoid: "Begging, explaining, pushing, showing disappointment"

  never_do:
    - "Thank them excessively"
    - "Ask 'Does that make sense?'"
    - "Say 'Please let me know'"
    - "Follow up with 'Just checking in'"
    - "Send document without new value"

  time_frame_close:
    script: |
      "I should mention - we're finalizing this [timeframe].
      After that, [consequence].
      I don't want you to miss this, but I also respect your process.
      What makes sense as a next step?"
```

---

## Phase 5: Eliminating Neediness

### Step 5.1: The Neediness Audit

> "Neediness is the Number One Deal Killer. Showing signs of neediness is about the worst thing you can do to your pitch."

**Self-Assessment:**

```yaml
neediness_audit:
  symptoms_to_eliminate:
    language:
      - "Thank you so much for your time" → Replace with: "[State next step]"
      - "Please let me know" → Replace with: "[Set specific follow-up]"
      - "Sorry to take up your time" → Delete entirely
      - "Does that make sense?" → Replace with: "Here's what's next"
      - "I hope this works for you" → Replace with: "Let me know by [date]"

    behavior:
      - Checking for approval during pitch → Keep moving confidently
      - Excessive nodding → Neutral, confident demeanor
      - Nervous laughter → Comfortable silence
      - Rushing when they seem impatient → Slow down, use your time frame
      - Over-explaining → State once, move on

    follow_up:
      - "Just checking in" → "[New value] I thought you'd find relevant"
      - "Have you had a chance to think?" → "[Deadline] is approaching"
      - Multiple emails with no response → Single message, then silence
```

### Step 5.2: The Three-Step Formula

**Template:**

```yaml
eliminate_neediness:
  step_1_walk_away_readiness:
    mindset: "I am completely willing to walk away from this deal"
    preparation:
      - "What's my BATNA (Best Alternative to Negotiated Agreement)?"
      - "Will I be okay if this doesn't close?"
      - "What other opportunities do I have?"

    your_batna: "[Your alternative if this doesn't work]"

    affirmation: "This deal doesn't define my success."

  step_2_eliminate_pleading_words:
    remove_from_vocabulary:
      - "Thank you" (excessive)
      - "Please"
      - "Sorry"
      - "Hope"
      - "Maybe"
      - "Just" (as in "I'm just following up")

    replace_with:
      - Direct statements
      - Confident assertions
      - Clear next steps

  step_3_disconnect_happiness:
    principle: "Your happiness cannot depend on their decision"

    mental_exercise: |
      Before the pitch, visualize:
      1. They say yes - you are calm, professional
      2. They say no - you are calm, professional
      3. Either way, you are fine

    during_pitch: "Remember: you're evaluating THEM as much as they're evaluating you"
```

### Step 5.3: Neediness Prevention Tactics

```yaml
neediness_prevention:
  time_frame:
    tactic: "Always enter with YOUR time constraint"
    message: "You are needed elsewhere"
    script: "I have [time] before my next meeting"

  withdrawal:
    tactic: "At crucial moment, pull back when they expect you to push"
    message: "You don't need this deal"
    script: "This might not be the right fit, and that's okay"

  excellence_focus:
    tactic: "Show what you do well, don't ask for validation"
    message: "Judge based on excellence, not persuasion"
    behavior: "Demonstrate, don't explain"

  silence:
    tactic: "Let silence work for you"
    message: "You're comfortable, not anxious"
    after_key_points: "[Pause 3-5 seconds. Let it land.]"
```

---

## Phase 6: Pitch Script Assembly

### Step 6.1: Complete Script Template

**Assemble your pitch components:**

```yaml
complete_pitch_script:
  minutes_1_5_set_frame:
    time_constraint: "[Your time statement]"
    frame_setter: "[Your perspective/lens]"
    authority_signal: "[Brief credential]"
    status_tip_off: "[Insider language]"
    local_star_power: "[Your domain expertise]"

  minutes_5_8_tell_story:
    big_idea: "[For WHO + doing WHAT + creating RESULT]"
    three_forces: "[Market forces creating opportunity]"
    narrative_setup: "[The problem/world as it is]"
    narrative_tension: "[Stakes and urgency]"

  minutes_8_12_reveal_intrigue:
    man_in_jungle_story: "[Your intrigue story]"
    crisis_point: "[The dangerous moment]"
    your_action: "[What you did]"
    cliff_hanger: "[Leave unresolved]"

  minutes_12_15_offer_prize:
    prize_positioning: "[Why you are the prize]"
    make_them_qualify: "[Question that flips dynamic]"
    withdrawal_if_needed: "[Your graceful pullback]"

  minutes_15_17_nail_hookpoint:
    resolve_intrigue: "[Finish the story]"
    hot_cognition_stack: "[Intrigue + Prize + Time + Moral Authority]"
    emotional_peak: "[The 'I want this' moment]"

  minutes_17_20_get_decision:
    direct_ask: "[Your ask]"
    time_frame_close: "[Urgency and deadline]"
    response_handling: "[How you'll handle each response]"
```

### Step 6.2: Counter-Frame Quick Reference

**Keep these ready:**

```yaml
counter_frame_cards:
  vs_power_frame:
    recognition: "They assert ego/authority"
    counter: "Defiance + Humor"
    script: "[Your prepared power-bust]"

  vs_time_frame:
    recognition: "They constrain your time"
    counter: "Set YOUR constraint first"
    script: "[Your time constraint statement]"

  vs_analyst_frame:
    recognition: "They demand data/numbers"
    counter: "Intrigue Frame"
    script: "We can review the details later. But first, let me tell you about..."

  vs_any_frame:
    universal_counter: "Prize Frame"
    principle: "You are the prize. Flip any dynamic with this."
```

---

## Phase 7: Validation Checklist

### Step 7.1: Pre-Pitch Checklist

```yaml
pre_pitch_validation:
  croc_brain_optimization:
    - [ ] Message is simple and concrete
    - [ ] Novelty factors are clear
    - [ ] No threat triggers
    - [ ] Hot cognition drivers identified

  status_preparation:
    - [ ] Local Star Power domain defined
    - [ ] Flash Roll scripted (90 seconds)
    - [ ] Status tip-off ready
    - [ ] Beta traps anticipated

  frame_strategy:
    - [ ] Your frame clearly defined
    - [ ] Counter-frames prepared for power/time/analyst
    - [ ] Frame stack ordered
    - [ ] Prize frame positioning solid

  neediness_elimination:
    - [ ] Walk-away readiness affirmed
    - [ ] Pleading words removed from script
    - [ ] Happiness disconnected from outcome
    - [ ] BATNA identified
```

### Step 7.2: Pitch Quality Checklist

```yaml
pitch_quality_validation:
  structure:
    - [ ] Total time under 20 minutes
    - [ ] S-T-R-O-N-G components all present
    - [ ] Clear transitions between phases
    - [ ] No data dumps or analysis sections

  frame_control:
    - [ ] Frame established in first 5 minutes
    - [ ] Counter-frames ready
    - [ ] Prize frame active throughout
    - [ ] Time frame YOU control

  emotional_engagement:
    - [ ] Hot cognition triggers present
    - [ ] Intrigue story with cliff-hanger
    - [ ] Hookpoint moment defined
    - [ ] Cold cognition deflection ready

  closing:
    - [ ] Direct ask prepared
    - [ ] Response handling scripted
    - [ ] Zero neediness in language
    - [ ] Follow-up maintains prize frame
```

### Step 7.3: Anti-Pattern Check

**Verify you're NOT doing these:**

```yaml
anti_patterns_check:
  - [ ] NOT pitching longer than 20 minutes
  - [ ] NOT starting with data/spreadsheets
  - [ ] NOT reacting to their power moves
  - [ ] NOT explaining your authority (show, don't tell)
  - [ ] NOT chasing them
  - [ ] NOT seeking validation
  - [ ] NOT debating numbers during pitch
  - [ ] NOT accepting beta traps
  - [ ] NOT using "thank you" / "please" / "sorry" excessively
  - [ ] NOT following up with "just checking in"
```

---

## Phase 8: Output Template

### Complete Pitch Document

```markdown
# [TITLE] - Pitch Using STRONG Method

## Pitch Overview
- **Duration:** 20 minutes
- **Target:** [Who you're pitching to]
- **Ask:** [What you want]
- **Prize Position:** [Why you're the prize]

## Pre-Pitch Setup

### Status Strategy
- **Your Local Star Power:** [Domain expertise]
- **Status Tip-Off:** [Insider phrase]
- **Flash Roll (90s):** [Technical mastery script]

### Frame Strategy
- **Your Frame:** [Your perspective]
- **Power-Bust Ready:** [Counter-script]
- **Time Frame:** [Your constraint]
- **Intrigue Story:** [Man in the jungle]

---

## The STRONG Pitch Script

### S - SET THE FRAME (Minutes 1-5)
[Your complete opening script]

### T - TELL THE STORY (Minutes 5-8)
[Your Big Idea and narrative]

### R - REVEAL THE INTRIGUE (Minutes 8-12)
[Your intrigue story with cliff-hanger]

### O - OFFER THE PRIZE (Minutes 12-15)
[Your prize positioning and qualification]

### N - NAIL THE HOOKPOINT (Minutes 15-17)
[Your hot cognition stack and emotional peak]

### G - GET THE DECISION (Minutes 17-20)
[Your ask and response handling]

---

## Counter-Frame Quick Cards

| Their Frame | Your Counter |
|-------------|--------------|
| Power Frame | [Your power-bust] |
| Time Frame | [Your time constraint] |
| Analyst Frame | [Your intrigue redirect] |

## Neediness Elimination
- **BATNA:** [Your alternative]
- **Removed Words:** thank you, please, sorry, hope, just
- **Mindset:** I am evaluating them as much as they're evaluating me

---

## Post-Pitch Protocol

### If YES:
- [Next step without over-thanking]

### If NEED TO THINK:
- [Hot cognition redirect]

### If NO:
- [Graceful exit maintaining status]

### Follow-Up:
- [Value-add only, no "checking in"]
```

---

## Sources

### Primary Sources
1. Klaff, Oren. "Pitch Anything: An Innovative Method for Presenting, Persuading, and Winning the Deal." McGraw-Hill, 2011.
2. Klaff, Oren. "Flip the Script: Getting People to Think Your Idea Is Their Idea." Portfolio/Penguin, 2019.

### Secondary Sources
3. Shortform - Pitch Anything Summary: https://www.shortform.com/blog/pitch-anything-oren-klaff/
4. The Power Moves - Pitch Anything Framework: https://thepowermoves.com/pitch-anything/
5. Breakthrough Marketing Secrets: https://www.breakthroughmarketingsecrets.com/blog/how-to-pitch-anything-in-20-minutes-according-to-oren-klaff/
6. Well That Makes Sense - Frame Control: https://www.wellthatmakessense.com/you_must_own_the_frame/
7. Viktori - Mastering Pitch Anything: https://viktori.co/oren-klaff-pitch-anything-technique/
8. Paubox - Pitch Anything Takeaways: https://www.paubox.com/blog/pitch-anything-oren-klaff-takeaways
9. GetStoryShots - Pitch Anything Summary: https://www.getstoryshots.com/books/pitch-anything-summary/

---

**Task Version:** 1.0.0
**Created:** 2026-01-30
**Agent:** @oren-klaff
**Lines:** 900+
**Quality:** Research-backed, based on primary sources
