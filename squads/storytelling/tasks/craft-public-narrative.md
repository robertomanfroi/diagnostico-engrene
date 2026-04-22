# Task: Craft Public Narrative

**Task ID:** craft-public-narrative
**Version:** 1.0.0
**Agent:** @marshall-ganz
**Purpose:** Guide leaders through creating their complete Public Narrative (Story of Self, Story of Us, Story of Now) to inspire action
**Duration:** 45-90 minutes
**Mode:** Interactive with structured elicitation

---

## Overview

This task guides users through Marshall Ganz's complete Public Narrative methodology - a leadership practice that translates values into action through storytelling. By the end, participants will have crafted three interconnected stories that move people to join them in collective action.

**The Core Insight:** Values inspire action through emotion. Stories allow us to express our values not as abstract principles, but as lived experience - and that's what moves people to act.

**The Three Stories:**
1. **Story of Self** - Why YOU are called to leadership
2. **Story of Us** - The shared values that bind your community
3. **Story of Now** - The urgent challenge that demands action TODAY

Each story follows the Challenge-Choice-Outcome structure.

---

## Prerequisites

Before starting this task, the user should:
- [ ] Have a cause, issue, or change they want to create
- [ ] Be willing to reflect on personal experiences
- [ ] Understand they are learning a PRACTICE, not writing a script
- [ ] Commit to the iterative process of telling, listening, and retelling

---

## Task Structure

```
Phase 1: GROUNDING (5-10 minutes)
├── Understand the purpose of public narrative
├── Identify the change you want to create
└── Connect to the values driving your work

Phase 2: STORY OF SELF (15-25 minutes)
├── Identify choice points in your life
├── Select the most relevant challenge
├── Craft Challenge-Choice-Outcome
└── Tell your 2-minute story

Phase 3: STORY OF US (15-20 minutes)
├── Define your "us" (the community)
├── Identify shared values and experiences
├── Find community choice points
└── Craft the collective narrative

Phase 4: STORY OF NOW (10-15 minutes)
├── Name the urgent challenge
├── Present the choice facing the community
├── Inspire hope
└── Define concrete first action

Phase 5: INTEGRATION (10-15 minutes)
├── Weave the three stories together
├── Ensure natural flow
├── Practice the complete narrative
└── Receive feedback and refine

OUTPUT: Complete Public Narrative (6-8 minutes total)
```

---

## Phase 1: Grounding

**Duration:** 5-10 minutes
**Purpose:** Establish context and connect to purpose

### Step 1.1: Introduce the Framework

```markdown
FACILITATOR SCRIPT:

"Public narrative is a leadership practice - not a script to memorize, but a skill to develop
through practice. The goal is to move people to join you in action on behalf of a shared purpose.

The key insight: VALUES INSPIRE ACTION THROUGH EMOTION. When we share our values as lived
experience - not abstract principles - we create the emotional connection that moves people to act.

We'll work through three interconnected stories:
- Story of Self: Why YOU were called to this work
- Story of Us: Why WE are called together
- Story of Now: Why we must act NOW

Each story follows the same structure: Challenge → Choice → Outcome

By the end, you'll have a 6-8 minute narrative that inspires others to join your cause."
```

### Step 1.2: Identify Your Purpose

**Elicitation Questions:**

```yaml
elicit: true
format: conversational
questions:
  - question: "What is the change you want to create in the world?"
    purpose: Identify the cause/issue
    probe: "Be specific - what would be different if you succeeded?"

  - question: "Who are the people you're trying to reach and motivate?"
    purpose: Define the audience
    probe: "Who needs to take action? What do they care about?"

  - question: "Why does this matter to you personally?"
    purpose: Connect to values
    probe: "What would it mean if this change happened? What if it didn't?"
```

**Capture:**
- The specific change/cause
- The target audience
- Initial values connection

### Step 1.3: Values Inventory

**Facilitator Prompt:**

```markdown
"Let's identify the VALUES that drive your commitment to this cause. Values aren't abstract
concepts - they're emotional experiences. Which of these resonate with why you do this work?

Common values that drive action:
□ Justice - fairness, equality, rights
□ Community - belonging, solidarity, togetherness
□ Dignity - respect, worth, recognition
□ Freedom - autonomy, choice, liberation
□ Compassion - caring, empathy, service
□ Hope - possibility, change, future
□ Courage - standing up, risk, conviction
□ Truth - honesty, transparency, integrity
□ Love - connection, care, devotion
□ Responsibility - duty, accountability, stewardship

Which 2-3 values most strongly connect to your work? Where do those values come from in your life?"
```

**Output from Phase 1:**
```yaml
grounding_summary:
  cause: "[specific change sought]"
  audience: "[who needs to be motivated]"
  core_values:
    - value: "[value 1]"
      origin: "[where it comes from]"
    - value: "[value 2]"
      origin: "[where it comes from]"
```

---

## Phase 2: Story of Self

**Duration:** 15-25 minutes
**Purpose:** Discover and craft your personal calling story

### The Theory

```markdown
FACILITATOR EXPLANATION:

"Your Story of Self explains WHY YOU were called to what you have been called to. It's not
your whole life story - it's a focused narrative about a CHOICE POINT that reveals your values.

A choice point is a moment when:
- You faced a challenge that demanded a response
- You had to make a decision under uncertainty
- The outcome taught you something about who you are

We construct our identity through these choice points. When you share one authentically,
others can connect with your values and understand why you're trustworthy to lead.

Remember: The goal is NOT comprehensive autobiography. It's ONE key moment that shows
your values in action."
```

### Step 2.1: Identify Choice Points

**Elicitation Questions:**

```yaml
elicit: true
format: guided_reflection
questions:
  - question: "Think back to when you FIRST became aware of this issue or cause. What was happening? What did you see, hear, or experience?"
    purpose: Find origin moment
    time_given: "2-3 minutes reflection"

  - question: "When did you feel you HAD to do something about it? What was the trigger?"
    purpose: Find activation moment
    probe: "What made it YOUR responsibility?"

  - question: "Was there a specific moment when you made a choice - even a small one - to engage with this issue?"
    purpose: Find choice point
    probe: "It might be: signing up, speaking out, changing direction, taking a risk..."

  - question: "What other moments in your life shaped the values that led you here?"
    purpose: Explore backstory
    sources:
      - "Family and childhood experiences"
      - "Role models and mentors"
      - "Challenges you've overcome"
      - "Moments of injustice witnessed"
      - "Experiences of community and belonging"
```

### Step 2.2: Select Your Choice Point

**Facilitator Guidance:**

```markdown
"From what you've shared, let's identify the MOST POWERFUL choice point for your Story of Self.

The best choice point:
✓ Reveals your core values in action
✓ Shows you facing a real challenge
✓ Demonstrates a clear choice you made
✓ Connects to why you're doing this work now
✓ Can be told in 2 minutes with vivid details

Which moment feels most authentic and connected to your current work?"
```

**Selection Criteria:**
```yaml
evaluate_choice_points:
  - criterion: "Values visibility"
    question: "Does this moment clearly reveal your core values?"
  - criterion: "Challenge clarity"
    question: "Is there real tension, uncertainty, or risk?"
  - criterion: "Choice specificity"
    question: "Can you point to a specific decision you made?"
  - criterion: "Outcome meaning"
    question: "Did you learn something that shapes who you are today?"
  - criterion: "Current relevance"
    question: "Does it connect to why you're leading this work now?"
```

### Step 2.3: Craft the Challenge

**Elicitation:**

```yaml
elicit: true
format: deep_dive
focus: "CHALLENGE component"

questions:
  - question: "Set the scene. Where were you? When was this?"
    purpose: Ground in specifics

  - question: "What was the challenge you faced?"
    purpose: Name the challenge

  - question: "WHY did you feel it was a challenge?"
    purpose: Deepen emotional connection
    probe: "What was at stake?"

  - question: "What was so challenging about it?"
    purpose: Explore the tension
    probe: "What made this hard? What were you risking?"

  - question: "Why was it YOUR challenge?"
    purpose: Establish ownership
    probe: "Why couldn't you walk away or let someone else handle it?"
```

**Craft the Challenge Paragraph:**

```markdown
TEMPLATE:
"It was [WHEN/WHERE]. I was [CONTEXT]. Then [CHALLENGE EMERGED].
What made it so difficult was [SPECIFIC DIFFICULTY].
I couldn't ignore it because [WHY IT WAS YOURS]."

EXAMPLE:
"It was the summer of 1964, and I was a student at Harvard. I heard about the Freedom Summer
project in Mississippi - hundreds of volunteers going south to register Black voters.
The challenge was clear: people were risking their lives for democracy, and I had to decide
if I would join them. What made it hard was the real danger - three volunteers had just been
killed. I couldn't ignore it because everything I believed about justice and equality was
meaningless if I wasn't willing to act on it."
```

### Step 2.4: Craft the Choice

**Elicitation:**

```yaml
elicit: true
format: deep_dive
focus: "CHOICE component"

questions:
  - question: "What did you decide to do?"
    purpose: Name the specific choice

  - question: "Why did you make that choice?"
    purpose: Connect to values
    probe: "What values guided your decision?"

  - question: "Where did you find the COURAGE to make that choice?"
    purpose: Surface emotional resources
    probe: "What gave you strength? Who supported you?"

  - question: "Where did you find the HOPE that it would matter?"
    purpose: Surface belief in possibility
    probe: "What made you believe your action could make a difference?"
```

**Craft the Choice Paragraph:**

```markdown
TEMPLATE:
"I decided to [SPECIFIC CHOICE].
I made that choice because [VALUES/REASONS].
I found the courage because [SOURCE OF COURAGE].
I had hope because [SOURCE OF HOPE]."

EXAMPLE:
"I decided to drop out of Harvard and go to Mississippi. I made that choice because if I
truly believed in equality, I had to be willing to fight for it - not just study it.
I found the courage from my parents, who had always taught me to stand up for what's right,
even when it's hard. I had hope because I saw hundreds of others making the same choice -
I wasn't alone."
```

### Step 2.5: Craft the Outcome

**Elicitation:**

```yaml
elicit: true
format: deep_dive
focus: "OUTCOME component"

questions:
  - question: "What happened as a result of your choice?"
    purpose: Name the outcome

  - question: "How did the outcome FEEL?"
    purpose: Access emotional truth
    probe: "Not what you thought - what did you FEEL?"

  - question: "Why did it feel that way?"
    purpose: Deepen emotional understanding

  - question: "What did this experience TEACH you?"
    purpose: Extract the moral
    probe: "What do you know now that you didn't know before?"
```

**Craft the Outcome Paragraph:**

```markdown
TEMPLATE:
"What happened was [OUTCOME].
I felt [EMOTION] because [REASON FOR FEELING].
What I learned was [MORAL/LESSON].
And that's why I'm still doing this work today."

EXAMPLE:
"What happened was transformative. I spent the summer registering voters, and I experienced
both the terror of violence and the power of community organizing. I felt alive in a way I
never had before - because I was finally living my values, not just thinking about them.
What I learned was that ordinary people, working together, CAN change the world - but only
if they're willing to take risks and build power together. And that's why I've spent my
whole life teaching people how to organize."
```

### Step 2.6: Tell Your Story of Self

**Practice Instructions:**

```markdown
FACILITATOR PROMPT:

"Now put your Challenge, Choice, and Outcome together into a 2-minute Story of Self.

Guidelines:
- Start with a specific moment (not "I've always believed...")
- Use concrete details - images, sounds, feelings
- Show your values through your actions, not by stating them
- Let the outcome connect to why you're here today

Take 3 minutes to organize your thoughts, then tell me your Story of Self."
```

**Time:** 2 minutes (firm limit)

**Feedback Framework:**

```yaml
feedback_questions:
  challenge:
    - "I could feel the challenge when you said..."
    - "What made it so hard for YOU specifically?"
    - "Can you add more sensory details to that moment?"

  choice:
    - "The choice became clear when..."
    - "Where did you find the courage/hope? Can we hear more about that?"
    - "What were you risking by making that choice?"

  outcome:
    - "The lesson that landed for me was..."
    - "How did that experience change you?"
    - "How does that connect to what you're doing now?"

  overall:
    - "The values I heard were... Did I get that right?"
    - "The moment that moved me most was..."
    - "What would make this story even more vivid?"
```

**Output from Phase 2:**
```yaml
story_of_self:
  challenge: "[2-3 sentences]"
  choice: "[2-3 sentences]"
  outcome: "[2-3 sentences]"
  values_revealed: ["value1", "value2"]
  duration: "~2 minutes"
```

---

## Phase 3: Story of Us

**Duration:** 15-20 minutes
**Purpose:** Build collective identity and shared values

### The Theory

```markdown
FACILITATOR EXPLANATION:

"Your Story of Us communicates the values SHARED by those you hope to motivate to act.
It creates collective identity - the sense that 'we' are in this together.

We participate in many 'us's: family, community, faith, organization, profession, nation,
movement. Your Story of Us evokes the specific 'us' you're calling to action.

Just like Story of Self, Story of Us uses Challenge-Choice-Outcome - but the CHARACTER
is the community, not just you. You're telling a story about shared experience.

CRITICAL: The challenge for 21st-century leaders is to tell a Story of Us that INCLUDES
people of all backgrounds who are fighting for the same cause - not one that creates enemies
of those outside the 'magic circle.'"
```

### Step 3.1: Define Your "Us"

**Elicitation:**

```yaml
elicit: true
format: structured
questions:
  - question: "Who is the 'us' you're calling to action?"
    purpose: Define the community
    options:
      - "A specific organization or group"
      - "People who share a common identity"
      - "People affected by a common problem"
      - "People who share common values"
      - "A movement of people seeking change"
    probe: "Be specific - who exactly are you trying to bring together?"

  - question: "What makes this group a 'we'? What do they share?"
    purpose: Identify binding elements
    probe: "Experiences? Values? Aspirations? Challenges?"

  - question: "Who might feel excluded from this 'us'? How can you be more inclusive?"
    purpose: Check for exclusion
    warning: "Stories of Us that create enemies often backfire"
```

### Step 3.2: Identify Shared Values and Experiences

**Elicitation:**

```yaml
elicit: true
format: exploration
questions:
  - question: "What VALUES do you share with this community?"
    purpose: Name shared values
    probe: "Not what you wish they valued - what do they actually value?"

  - question: "What EXPERIENCES have shaped this community?"
    purpose: Find shared history
    categories:
      - "Founding moments"
      - "Crises overcome"
      - "Triumphs celebrated"
      - "Injustices suffered"
      - "Heroes honored"

  - question: "What gives this community HOPE?"
    purpose: Identify aspirations
    probe: "What do they believe is possible? What do they want to achieve?"

  - question: "What threatens what this community cares about?"
    purpose: Identify shared challenges
    probe: "What keeps them up at night? What do they fear losing?"
```

### Step 3.3: Find Community Choice Points

**Facilitator Guidance:**

```markdown
"Now let's find a CHOICE POINT in the community's experience - a moment when 'we'
faced a challenge, made a choice, and experienced an outcome that defines who we are.

These could be:
- A FOUNDING MOMENT: When the community came together
- A CRISIS: When we were tested and showed our values
- A TRIUMPH: When we achieved something together
- A TURNING POINT: When we changed course
- AN ACT OF RESILIENCE: When we persevered through difficulty

Which moment in your community's history best captures who 'we' are and what 'we' value?"
```

**Selection Questions:**

```yaml
elicit: true
questions:
  - question: "What is a moment in this community's history that shows who 'we' are?"
    purpose: Identify community choice point

  - question: "What was the CHALLENGE the community faced in that moment?"
    purpose: Name community challenge

  - question: "What CHOICE did the community make?"
    purpose: Name community decision

  - question: "What was the OUTCOME? What did 'we' learn about ourselves?"
    purpose: Name community outcome
```

### Step 3.4: Craft the Story of Us

**Structure:**

```markdown
STORY OF US TEMPLATE:

CHALLENGE:
"As [COMMUNITY], we have always [SHARED VALUE/EXPERIENCE].
But there came a time when [CHALLENGE EMERGED].
We faced [SPECIFIC THREAT TO VALUES]."

CHOICE:
"In that moment, we chose to [COLLECTIVE ACTION].
We did this because [VALUES DRIVING CHOICE].
Together, we [SPECIFIC ACTIONS TAKEN]."

OUTCOME:
"What happened showed us who we really are.
We [OUTCOME ACHIEVED/LESSON LEARNED].
And that's why today, we [CONNECTION TO CURRENT WORK]."
```

**Example:**

```markdown
"As farmworkers, we had always known the value of hard work - we put food on America's
tables with our own hands. But in 1965, we faced a crisis. The grape growers refused to
pay us a living wage, and when we asked for basic dignity, they called us troublemakers.

In that moment, we chose to strike. We chose to march. We chose to boycott. We did this
because we believed that our labor had value, and that together, we had power that we
didn't have alone. For five years, we walked picket lines, fasted, and organized.

What happened showed us who we really are. We won. Not because we were the most powerful,
but because when working people stand together, we cannot be ignored. And that's why today,
we continue to fight for the dignity of all workers - because we know what's possible when
we organize together."
```

### Step 3.5: Tell Your Story of Us

**Practice Instructions:**

```markdown
FACILITATOR PROMPT:

"Now tell me your Story of Us - the narrative that creates collective identity and
reminds your community who 'we' are and what 'we' value.

Guidelines:
- Speak as 'we', not 'you' or 'they'
- Ground the story in specific shared experience
- Show values through collective action
- Make it INCLUSIVE - invite people into the 'us'
- Connect to the current moment

Take 3 minutes to organize, then tell me your Story of Us in about 2 minutes."
```

**Feedback Framework:**

```yaml
feedback_questions:
  - "I felt included in the 'us' when you said..."
  - "The shared value that came through strongest was..."
  - "The moment that showed who 'we' are was..."
  - "Is there anyone who might feel excluded? How could you include them?"
  - "How does this story connect to the action you're calling for?"
```

**Output from Phase 3:**
```yaml
story_of_us:
  community_defined: "[who is the 'us']"
  challenge: "[2-3 sentences]"
  choice: "[2-3 sentences]"
  outcome: "[2-3 sentences]"
  shared_values: ["value1", "value2"]
  duration: "~2 minutes"
```

---

## Phase 4: Story of Now

**Duration:** 10-15 minutes
**Purpose:** Create urgency and call to action

### The Theory

```markdown
FACILITATOR EXPLANATION:

"Your Story of Now transforms the present moment into one of CHALLENGE, HOPE, and CHOICE.

This is 'the fierce urgency of now.' After sharing values and aspirations, we realize
the world is NOT as it ought to be. That gap between what IS and what OUGHT to be
is a challenge to everything we value.

The Story of Now must accomplish four things:
1. Name the URGENT CHALLENGE facing the community
2. Present the CHOICE that must be made
3. Inspire HOPE that change is possible
4. Offer a CONCRETE FIRST STEP people can take immediately

The balance is critical: Create URGENCY that overcomes inertia, while inspiring HOPE
that overcomes fear. Without urgency, people don't move. Without hope, people despair."
```

### Step 4.1: Name the Urgent Challenge

**Elicitation:**

```yaml
elicit: true
format: structured
questions:
  - question: "What is the urgent challenge facing your community RIGHT NOW?"
    purpose: Name the challenge
    probe: "Why must we act NOW and not later?"

  - question: "How does this challenge THREATEN the values we just discussed?"
    purpose: Connect to values
    probe: "What do we stand to lose if we don't act?"

  - question: "What makes this moment different? Why is NOW the time?"
    purpose: Establish urgency
    sources:
      - "A window of opportunity closing"
      - "A threat intensifying"
      - "A tipping point approaching"
      - "A decision being made soon"
      - "Momentum building that must be captured"

  - question: "What happens if we DON'T act?"
    purpose: Clarify stakes
    warning: "Be honest about consequences without inducing hopelessness"
```

### Step 4.2: Present the Choice

**Elicitation:**

```yaml
elicit: true
format: binary_frame
questions:
  - question: "What is the choice facing the community?"
    purpose: Frame the decision
    format: "We can either [OPTION A] or [OPTION B]"
    note: "Make it clear, not complicated. Binary choices mobilize."

  - question: "Why is this choice so important?"
    purpose: Elevate the stakes
    probe: "What's at stake in this decision?"

  - question: "Why should people choose to act with you?"
    purpose: Make the case for action
    probe: "What do you offer that makes action worthwhile?"
```

### Step 4.3: Inspire Hope

**Elicitation:**

```yaml
elicit: true
format: balance_framework
note: "Hope is the antidote to fear. Without it, urgency becomes despair."

questions:
  - question: "Why should people believe change is possible?"
    purpose: Ground hope in evidence
    probe: "What gives you confidence we can succeed?"

  - question: "What resources does the community have?"
    purpose: Identify assets
    categories:
      - "People power"
      - "Stories of past success"
      - "Allies and supporters"
      - "Skills and talents"
      - "Moral authority"

  - question: "What have we already achieved?"
    purpose: Build on success
    probe: "Even small wins matter - what progress have we made?"

  - question: "What would success look like?"
    purpose: Paint the vision
    probe: "Help people see the world we're fighting for"
```

### Step 4.4: Define Concrete First Action

**Elicitation:**

```yaml
elicit: true
format: specific_action
critical: "Every Story of Now MUST end with a concrete first step"

questions:
  - question: "What is the FIRST THING you're asking people to do?"
    purpose: Define immediate action
    criteria:
      - "Specific (not vague)"
      - "Achievable (not overwhelming)"
      - "Immediate (can be done NOW)"
      - "Collective (joins people together)"
      - "Meaningful (contributes to the goal)"

  - question: "How can people take this action TODAY?"
    purpose: Remove barriers
    probe: "Make it as easy as possible to say yes"

  - question: "What happens after they take this first step?"
    purpose: Show pathway
    probe: "How does this action lead to more engagement?"
```

### Step 4.5: Craft the Story of Now

**Structure:**

```markdown
STORY OF NOW TEMPLATE:

URGENT CHALLENGE:
"Right now, we face [URGENT CHALLENGE].
This threatens everything we value because [CONNECTION TO VALUES].
If we don't act, [CONSEQUENCES].
And the time to act is NOW because [WHY NOW]."

THE CHOICE:
"We have a choice to make.
We can either [OPTION A - inaction/status quo]
Or we can [OPTION B - collective action].
The question is: which will we choose?"

HOPE:
"I believe we can succeed because [REASONS FOR HOPE].
We have [RESOURCES/ASSETS].
We've already [PAST SUCCESSES].
And together, we can [VISION OF SUCCESS]."

CALL TO ACTION:
"So here's what I'm asking you to do.
[SPECIFIC FIRST STEP].
You can do this [HOW/WHEN].
Because when we [ACTION], we [IMPACT].
Will you join us?"
```

**Example:**

```markdown
"Right now, our community faces a crisis. The city is planning to close three neighborhood
schools next month - schools that have served our families for generations. This threatens
everything we value: our children's education, our community's future, our voice in decisions
that affect our lives. If we don't act, these schools will close, and our children will be
bused an hour away. The vote is in three weeks. We have three weeks.

We have a choice. We can accept this quietly, tell ourselves there's nothing we can do,
and watch our schools close. Or we can stand up together, make our voices heard, and fight
for our children's future. The question is: which will we choose?

I believe we can win this. Last year, parents in Springfield faced the same threat - and
they won. They showed up at every meeting, called every council member, and refused to
be ignored. We have the same power. We have 5,000 families in this district. We have
teachers who are with us. We have three weeks to show this city that we matter.

So here's what I'm asking you to do tonight. Before you leave, sign up to attend the
school board meeting on Tuesday. Put your name on that sheet, and commit to being there.
Because when 500 parents show up instead of 50, the board will have to listen. Will you
join us?"
```

### Step 4.6: Tell Your Story of Now

**Practice Instructions:**

```markdown
FACILITATOR PROMPT:

"Now tell me your Story of Now - the narrative that creates urgency and calls
people to immediate action.

Guidelines:
- Make the challenge URGENT - why now?
- Connect to the VALUES established in Self and Us
- Balance urgency with HOPE
- End with a SPECIFIC, ACHIEVABLE first step
- Make it clear how to say YES

Take 3 minutes to organize, then tell me your Story of Now in about 2 minutes."
```

**Feedback Framework:**

```yaml
feedback_questions:
  urgency:
    - "I felt the urgency when you said..."
    - "Is the 'why now' clear enough? Can you make it sharper?"

  hope:
    - "I felt hope when you said..."
    - "Is there enough hope to counter the fear? Too much?"

  action:
    - "The call to action was clear: [restate it]"
    - "Could I actually do this action right now?"
    - "What might stop someone from saying yes? How can you address that?"
```

**Output from Phase 4:**
```yaml
story_of_now:
  urgent_challenge: "[2-3 sentences]"
  the_choice: "[2-3 sentences]"
  hope: "[2-3 sentences]"
  call_to_action: "[specific, immediate action]"
  duration: "~2 minutes"
```

---

## Phase 5: Integration

**Duration:** 10-15 minutes
**Purpose:** Weave the three stories into one cohesive narrative

### Step 5.1: Review the Flow

**Structure Check:**

```markdown
PUBLIC NARRATIVE FLOW:

STORY OF SELF (2 min)
↓ "And that's why I care about this..."
STORY OF US (2 min)
↓ "And we're not alone - together we..."
STORY OF NOW (2 min)
↓ "Which brings us to today..."
CALL TO ACTION
"So will you join us?"

Total: 6-8 minutes
```

### Step 5.2: Create Transitions

**Facilitator Guidance:**

```markdown
"Now let's connect your three stories with natural transitions.

The transitions should:
- Flow naturally (not feel like three separate speeches)
- Connect the values across all three stories
- Build momentum toward the call to action

Common transition approaches:

SELF → US:
- "And I learned I wasn't alone..."
- "That experience taught me that we..."
- "What I discovered was that many of us..."

US → NOW:
- "Which is why what's happening now is so important..."
- "And today, we face a new challenge..."
- "That's the community I'm calling on today, because..."
```

### Step 5.3: Practice the Complete Narrative

**Full Run-Through:**

```markdown
FACILITATOR PROMPT:

"Now tell me your complete Public Narrative - Story of Self, Story of Us, Story of Now -
all together. Aim for 6-8 minutes total.

Remember:
- This is practice, not performance
- Focus on the emotional truth, not perfect words
- Let the stories flow into each other
- End with a clear call to action

I'll listen without interrupting, then give you feedback."
```

**Time:** 6-8 minutes

### Step 5.4: Comprehensive Feedback

**Feedback Framework:**

```yaml
comprehensive_feedback:
  overall:
    - "The value that came through across all three stories was..."
    - "The emotional arc felt like... [describe]"
    - "I was most moved when..."
    - "The call to action made me want to..."

  story_of_self:
    - "Your choice point was clear/needs work because..."
    - "I understood your values when you said..."
    - "The courage/hope source could be stronger by..."

  story_of_us:
    - "I felt included in the 'us' when..."
    - "The shared value was clear when..."
    - "The community choice point showed us who 'we' are by..."

  story_of_now:
    - "The urgency landed when you said..."
    - "The hope came through when..."
    - "The action step is [achievable/needs work] because..."

  transitions:
    - "The flow from Self to Us felt..."
    - "The flow from Us to Now felt..."
    - "One way to strengthen the connections..."

  refinement:
    - "If you could add one detail, add it to..."
    - "If you need to cut something, consider..."
    - "The next version should focus on..."
```

### Step 5.5: Revision and Polish

**Iteration Prompt:**

```markdown
"Based on the feedback, what would you like to revise?

Remember: Public narrative is learned by telling, listening, reflecting, and telling again.
This is an iterative process. Each time you tell your story:
- You'll make yourself clearer
- You'll adjust to different audiences
- You'll find better words for your truth

What changes do you want to make for the next telling?"
```

**Revision Focus Areas:**

```yaml
revision_areas:
  - area: "Specificity"
    question: "Where can you add more concrete details?"
  - area: "Emotional truth"
    question: "Where can you go deeper into how things felt?"
  - area: "Values clarity"
    question: "Are your values showing through actions, not just words?"
  - area: "Urgency/hope balance"
    question: "Is there enough urgency without despair? Enough hope without naivety?"
  - area: "Action clarity"
    question: "Is it crystal clear what you're asking people to do?"
```

---

## Final Output

### Deliverable: Complete Public Narrative

```yaml
public_narrative_output:
  metadata:
    author: "[user name]"
    cause: "[change sought]"
    audience: "[target community]"
    date_created: "[date]"

  story_of_self:
    duration: "~2 minutes"
    challenge: "[summary]"
    choice: "[summary]"
    outcome: "[summary]"
    values_revealed: ["value1", "value2"]
    full_text: |
      [Complete Story of Self text]

  story_of_us:
    duration: "~2 minutes"
    community: "[who is the 'us']"
    challenge: "[summary]"
    choice: "[summary]"
    outcome: "[summary]"
    shared_values: ["value1", "value2"]
    full_text: |
      [Complete Story of Us text]

  story_of_now:
    duration: "~2 minutes"
    urgent_challenge: "[summary]"
    the_choice: "[summary]"
    hope: "[summary]"
    call_to_action: "[specific action]"
    full_text: |
      [Complete Story of Now text]

  complete_narrative:
    total_duration: "6-8 minutes"
    full_text: |
      [Complete integrated narrative with transitions]

  quality_assessment:
    values_visible: true/false
    challenge_choice_outcome_present: true/false
    emotional_connection: strong/medium/weak
    urgency_hope_balance: balanced/needs_work
    action_specific: true/false
    inclusive_us: true/false

  next_steps:
    - "Practice telling to [specific audience]"
    - "Adapt for [specific context]"
    - "Record video version"
    - "Prepare 30-second and 5-minute versions"
```

---

## Quality Checklist

### Story of Self Checklist

- [ ] Focuses on ONE choice point (not whole life story)
- [ ] Challenge is specific and creates tension
- [ ] Choice reveals values through action
- [ ] Outcome includes emotional truth and lesson learned
- [ ] Connects to current work/leadership
- [ ] Duration: ~2 minutes
- [ ] Uses concrete details and images

### Story of Us Checklist

- [ ] "Us" is clearly defined
- [ ] Uses "we" language throughout
- [ ] Identifies shared values
- [ ] Includes community choice point (challenge-choice-outcome)
- [ ] Is INCLUSIVE (doesn't create enemies)
- [ ] Lifts up shared successes
- [ ] Duration: ~2 minutes

### Story of Now Checklist

- [ ] Urgent challenge is clear and timely
- [ ] Connects to values from Self and Us
- [ ] Choice is framed clearly (binary)
- [ ] Hope is grounded in evidence
- [ ] Call to action is SPECIFIC
- [ ] Call to action is ACHIEVABLE now
- [ ] Balance of urgency and hope
- [ ] Duration: ~2 minutes

### Integration Checklist

- [ ] Transitions flow naturally
- [ ] Values are consistent across all three stories
- [ ] Emotional arc builds toward action
- [ ] Complete narrative is 6-8 minutes
- [ ] Ends with clear call to action

---

## Adaptation Guide

### For Different Time Limits

**30 Seconds (Elevator Pitch):**
- One sentence each: Self, Us, Now
- Focus on values and action

**2 Minutes (Brief Introduction):**
- Condensed Self (30 sec)
- Brief Us (30 sec)
- Urgent Now + Action (60 sec)

**5 Minutes (Standard):**
- Full Self (90 sec)
- Full Us (90 sec)
- Full Now (2 min)

**15+ Minutes (Extended):**
- Deeper Self with more context
- Multiple Us examples
- Detailed Now with Q&A

### For Different Contexts

**One-on-One Conversation:**
- More conversational, less polished
- Invite their story too
- Ask for specific commitment

**Group Meeting:**
- Standard 6-8 minute version
- Pause for reactions
- Collective action step

**Public Speech:**
- More polished delivery
- Stronger opening hook
- Memorable closing

**Written/Email:**
- Adapt for reading
- Shorter paragraphs
- Clear action link

---

## Task Metadata

**Task ID:** craft-public-narrative
**Version:** 1.0.0
**Lines:** 700+
**Agent:** @marshall-ganz
**Research Foundation:** marshall-ganz-public-narrative-research.md
**Quality Gate:** All checklists must pass before completion

**Sources:**
- Harvard Kennedy School Public Narrative Program
- Leading Change Network Workshop Materials
- Bill Moyers Interview with Marshall Ganz
- "Why Stories Matter" (Sojourners Magazine)
- Camp Obama Training Documentation
