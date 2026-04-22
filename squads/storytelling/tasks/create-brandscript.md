# Task: Create StoryBrand BrandScript

**Task ID:** create-brandscript
**Version:** 1.0.0
**Agent:** @donald-miller
**Duration:** 30-60 minutes
**Mode:** Interactive with elicitation
**Output:** Complete BrandScript + One-Liner + Implementation Guidance

---

## Purpose

Create a complete StoryBrand BrandScript using Donald Miller's SB7 Framework. This task guides users through all seven elements of the StoryBrand methodology to produce clear, compelling brand messaging that positions the customer as the hero and drives action.

---

## Prerequisites

Before starting this task, gather the following information:

- [ ] Business name and industry
- [ ] Target customer description (who you serve)
- [ ] Primary product/service offering
- [ ] Any existing marketing materials (optional, for audit)
- [ ] Competitor awareness (optional)

---

## Inputs

| Parameter | Type | Required | Description | Example |
|-----------|------|----------|-------------|---------|
| `business_name` | string | Yes | Name of the business | "Smith Financial Advisors" |
| `industry` | string | Yes | Business category/industry | "Financial services" |
| `target_customer` | string | Yes | Description of ideal customer | "Professionals 45-60 approaching retirement" |
| `primary_offering` | string | Yes | Main product/service | "Retirement planning and wealth management" |
| `existing_tagline` | string | No | Current tagline if any | "Your partner in wealth" |
| `key_differentiator` | string | No | What makes you different | "Fee-only fiduciary advisor" |

---

## Output Structure

```yaml
brandscript_output:
  brandscript:
    character:
      who: "[Customer description]"
      wants: "[Primary desire]"
    problem:
      villain: "[Root cause personified]"
      external: "[Tangible problem]"
      internal: "[Emotional impact]"
      philosophical: "[Why it matters]"
    guide:
      empathy: "[Understanding statement]"
      authority: "[Proof of competence]"
    plan:
      name: "[Plan name]"
      steps:
        - "[Step 1]"
        - "[Step 2]"
        - "[Step 3]"
    cta:
      direct: "[Primary action]"
      transitional: "[Lead magnet offer]"
    failure:
      stakes:
        - "[What they lose 1]"
        - "[What they lose 2]"
        - "[What they lose 3]"
    success:
      external: "[Tangible outcomes]"
      internal: "[How they'll feel]"
      transformation: "[Who they become]"

  one_liner: "[Complete one-liner]"

  implementation:
    website_header: "[Header copy]"
    value_proposition: "[Key benefits]"
    email_subject_lines:
      - "[Subject 1]"
      - "[Subject 2]"
      - "[Subject 3]"
```

---

## Workflow Steps

### PHASE 1: DISCOVERY & CONTEXT

#### Step 1.1: Business Understanding

**Duration:** 5 minutes

**Actions:**
```yaml
gather_context:
  questions:
    - "What is your business name and what do you do?"
    - "Who is your ideal customer? Be as specific as possible."
    - "What is the primary product or service you offer?"
    - "Do you have any existing tagline or positioning statement?"
    - "What makes you different from competitors?"

  listen_for:
    - Industry and market context
    - Customer demographics and psychographics
    - Core value proposition
    - Unique differentiators
    - Current messaging challenges
```

**Elicit:** True

**Interaction Format:**
```
I'll help you create a complete StoryBrand BrandScript. Let's start by understanding your business.

Please answer these questions:

1. What is your business name and what do you do?
2. Who is your ideal customer? (Be specific - demographics, situation, needs)
3. What is your primary product or service?
4. Do you have a current tagline or positioning statement?
5. What makes you different from competitors?

Take your time - the more specific you are, the better your BrandScript will be.
```

---

### PHASE 2: THE SEVEN ELEMENTS

#### Step 2.1: Element 1 - CHARACTER (The Hero)

**Duration:** 5-7 minutes

**Principle Reference:**
> "The customer is the hero, not your brand."
> — StoryBrand Principle One

**Actions:**
```yaml
define_character:
  objective: "Identify what the customer WANTS - one clear, specific desire"

  questions:
    - "What does your customer want most that relates to what you offer?"
    - "What would success look like for them?"
    - "What is the gap between where they are now and where they want to be?"

  want_categories:
    conserve_resources:
      - "Save time"
      - "Save money"
      - "Reduce stress"
      - "Simplify life"
    gain_status:
      - "Be respected"
      - "Be admired"
      - "Be seen as successful"
      - "Gain recognition"
    accumulate:
      - "Make more money"
      - "Build wealth"
      - "Gain skills"
      - "Grow their business"
    meaning:
      - "Make a difference"
      - "Leave a legacy"
      - "Contribute"
      - "Have purpose"
    safety:
      - "Feel secure"
      - "Be protected"
      - "Have stability"
      - "Reduce uncertainty"
    belonging:
      - "Connect with others"
      - "Be part of something"
      - "Feel accepted"
      - "Have community"

  rules:
    - Identify ONE primary want (not multiple)
    - Make it specific and tangible
    - Ensure it relates to survival/thriving
    - Create clear "story gap"

  output_format: |
    CHARACTER:
    Who: [Specific customer description]
    Wants: [One clear, specific desire]
    Current State: [Where they are now]
    Desired State: [Where they want to be]
    Story Gap: [The distance they need to travel]
```

**Elicit:** True

**Interaction Format:**
```
## ELEMENT 1: CHARACTER (The Hero)

Remember: Your customer is the hero of this story, not your brand.

Based on what you've told me about your business, let me help you identify what your customer truly WANTS.

Customers typically want things that relate to:
- Conserving resources (saving time, money, stress)
- Gaining status (respect, recognition, success)
- Accumulating (wealth, skills, growth)
- Finding meaning (purpose, contribution, legacy)
- Achieving safety (security, stability, certainty)
- Belonging (connection, community, acceptance)

**Question:** What is the ONE thing your ideal customer wants most, that relates to what you offer?

Think about:
- What would success look like for them?
- What's the gap between where they are and where they want to be?
```

---

#### Step 2.2: Element 2 - PROBLEM (Three Levels)

**Duration:** 7-10 minutes

**Principle Reference:**
> "Companies tend to sell solutions to external problems, but customers buy solutions to internal problems."
> — StoryBrand Principle Two

**Actions:**
```yaml
define_problem:
  objective: "Identify problems at all three levels - External, Internal, Philosophical"

  level_1_external:
    definition: "The tangible, surface-level problem"
    questions:
      - "What is the obvious, observable problem your customer faces?"
      - "What would they point to if asked 'what's the problem?'"
      - "What tangible challenge are they dealing with?"
    characteristics:
      - Observable and measurable
      - The 'obvious' problem
      - Practical or physical need

  level_2_internal:
    definition: "How the external problem makes them FEEL"
    questions:
      - "How does this problem make your customer FEEL?"
      - "What emotions does this challenge create?"
      - "What frustration or fear does it generate?"
    common_feelings:
      - Frustrated
      - Overwhelmed
      - Confused
      - Anxious
      - Embarrassed
      - Insecure
      - Doubtful
      - Stressed
    key_insight: "This is what they actually BUY solutions for"

  level_3_philosophical:
    definition: "Why this matters in the grand scheme"
    questions:
      - "Why is this situation WRONG or unjust?"
      - "What 'should' be true that isn't?"
      - "Why does solving this matter beyond the individual?"
    formula: "People should... / It's not right that... / Everyone deserves..."

  villain:
    definition: "The root cause personified"
    questions:
      - "What is the ROOT CAUSE of their problem?"
      - "What or who is the 'bad guy' in this story?"
    examples:
      - "Complexity"
      - "Hidden fees"
      - "Time thieves"
      - "Outdated systems"
      - "Information overload"
    rules:
      - Single, clear identity
      - Root source of problem
      - Relatable to audience
      - Real, not abstract

  output_format: |
    PROBLEM:
    Villain: [Root cause personified]
    External: [Tangible, observable problem]
    Internal: [How it makes them feel]
    Philosophical: [Why it matters - the 'ought' statement]
```

**Elicit:** True

**Interaction Format:**
```
## ELEMENT 2: PROBLEM (Three Levels)

Now let's identify the problem your customer faces. This is CRUCIAL because:

> "Companies sell solutions to external problems, but customers BUY solutions to INTERNAL problems."

I need you to think about THREE levels of problem:

### Level 1: EXTERNAL PROBLEM
What is the tangible, obvious problem they face?
(Something you could point to or measure)

Example: "Don't have enough saved for retirement"

### Level 2: INTERNAL PROBLEM
How does this problem make them FEEL?
(The emotional impact - this is what they actually buy solutions for)

Common feelings: frustrated, overwhelmed, anxious, embarrassed, insecure, confused, stressed

Example: "Feel anxious and uncertain about the future"

### Level 3: PHILOSOPHICAL PROBLEM
Why does this matter? What SHOULD be true?
(The bigger 'why' - often starts with "People should..." or "It's not right that...")

Example: "Everyone deserves to enjoy the retirement they've worked their whole life for"

### THE VILLAIN
What is the root CAUSE of their problem? (Personify it)

Example: "Complexity" or "Hidden fees" or "Conflicting advice"

**Please describe:**
1. External Problem:
2. Internal Problem (feelings):
3. Philosophical Problem (the 'ought' statement):
4. The Villain (root cause):
```

---

#### Step 2.3: Element 3 - GUIDE (Empathy + Authority)

**Duration:** 5-7 minutes

**Principle Reference:**
> "Customers aren't looking for another hero; they're looking for a guide."
> — StoryBrand Principle Three

**Actions:**
```yaml
define_guide:
  objective: "Position the brand as guide with BOTH empathy AND authority"

  empathy:
    definition: "Deep understanding of customer's problem and desire to help"
    formula: "We understand what it's like to [specific struggle]."
    questions:
      - "What do you truly understand about your customer's struggle?"
      - "How can you show you 'get it'?"
      - "What shared experience or understanding do you have?"
    is:
      - Understanding their struggles
      - Acknowledging their feelings
      - Showing you 'get it'
    is_not:
      - Pity
      - Talking about yourself
      - Generic 'we care' statements

  authority:
    definition: "Demonstrated competence to solve the problem"
    types:
      testimonials: "Customer success stories"
      statistics: "Numbers that prove results"
      awards: "Industry recognition, certifications"
      logos: "Client logos, media features"
      experience: "Years in business, projects completed"
      credentials: "Certifications, degrees, partnerships"
    questions:
      - "What proof do you have that you can solve their problem?"
      - "What results have you achieved for others?"
      - "What credentials or recognition do you have?"
      - "How many customers have you helped?"

  balance_rule: |
    CRITICAL: You must have BOTH empathy AND authority.
    - Too much empathy, no authority = "Nice, but can you help?"
    - Too much authority, no empathy = "Impressive, but do you understand me?"

  output_format: |
    GUIDE:
    Empathy Statement: "We understand what it's like to [struggle]."
    Authority Statement: "[Proof] that demonstrates [competence]."
```

**Elicit:** True

**Interaction Format:**
```
## ELEMENT 3: GUIDE (Empathy + Authority)

Your brand is NOT the hero. Your brand is the GUIDE - like Yoda to Luke, or Gandalf to Frodo.

A guide must demonstrate TWO things:

### EMPATHY
Show you understand their struggle.

Formula: "We understand what it's like to [specific struggle]."

Example: "We know how overwhelming it can feel to plan for retirement when there are so many unknowns."

**Question:** What empathy statement shows you truly understand your customer's struggle?

---

### AUTHORITY
Prove you can actually help them.

Ways to show authority:
- Testimonials (customer success stories)
- Statistics ("Helped 500+ families")
- Awards/Certifications
- Client logos
- Years of experience
- Credentials

Example: "For 20 years, we've helped over 500 families retire with confidence."

**Question:** What proof do you have that you can solve their problem?

---

IMPORTANT: You need BOTH. Empathy without authority = "Nice person, but can they help?"
Authority without empathy = "Impressive, but do they understand me?"

**Please provide:**
1. Your Empathy Statement:
2. Your Authority Statement (with specific proof):
```

---

#### Step 2.4: Element 4 - PLAN (Process + Agreement)

**Duration:** 5-7 minutes

**Principle Reference:**
> "Customers trust a guide who has a plan."
> — StoryBrand Principle Four

**Actions:**
```yaml
define_plan:
  objective: "Create clear plan that reduces risk and shows path forward"

  process_plan:
    definition: "Steps to do business with you"
    rules:
      - 3 steps is ideal (max 6)
      - Simple, clear language
      - Show complete path to success
      - Combine into phases if complex
    template:
      step_1: "[Engage/Discover - low commitment first step]"
      step_2: "[Customize/Plan - middle step showing your work]"
      step_3: "[Execute/Results - outcome they'll experience]"
    examples:
      financial:
        - "Schedule your free discovery call"
        - "We create your personalized retirement roadmap"
        - "Watch your wealth grow with confidence"
      it_services:
        - "Book your free tech audit"
        - "We implement your custom solution"
        - "Enjoy stress-free technology"
      consulting:
        - "Schedule a strategy session"
        - "We develop your custom plan"
        - "Execute with our support"

  agreement_plan:
    definition: "Promises that reduce fear and build trust"
    purpose: "Alleviate fears about doing business with you"
    types:
      risk_reduction: "Guarantees, refunds, warranties"
      quality_assurance: "Standards, testing, processes"
      shared_values: "Beliefs and commitments you share"
    questions:
      - "What fears might prevent someone from doing business with you?"
      - "What can you promise to address those fears?"
      - "What guarantees can you offer?"
    examples:
      - "No hidden fees, ever"
      - "Satisfaction guaranteed or money back"
      - "Same-day response"
      - "We don't leave until it works"

  naming_rule: |
    Give your plan a name to increase perceived value.
    Examples: "The Quick Start Plan", "The Peace of Mind Package"

  output_format: |
    PLAN:
    Name: "[Plan Name]"
    Process Steps:
    1. [First step]
    2. [Second step]
    3. [Third step]

    Agreement Promises:
    - [Promise 1]
    - [Promise 2]
    - [Promise 3]
```

**Elicit:** True

**Interaction Format:**
```
## ELEMENT 4: PLAN (Process + Agreement)

Now let's create a clear PLAN that shows customers how to work with you and reduces their fear.

### PROCESS PLAN (3 Steps)

What are the 3 simple steps someone takes to do business with you and get results?

Formula:
1. [Low commitment first step - engage/discover]
2. [Middle step - your work/customization]
3. [Final step - results/success]

Example (Financial Advisor):
1. Schedule your free discovery call
2. We create your personalized retirement roadmap
3. Watch your wealth grow with confidence

**Question:** What are your 3 process steps?

---

### AGREEMENT PLAN (Optional but Powerful)

What promises can you make that reduce their fear of doing business with you?

Think about:
- What might make them hesitate?
- What guarantee can you offer?
- What standards do you commit to?

Examples:
- "No hidden fees, ever"
- "Same-day response guarantee"
- "Satisfaction guaranteed or money back"
- "We explain everything in plain English"

**Question:** What 2-3 promises reduce their fear?

---

### NAME YOUR PLAN

Give your process a name to increase perceived value.

Examples: "The Quick Start Plan", "The Peace of Mind Package", "Our Client Success Process"

**Question:** What would you call your plan?

**Please provide:**
1. Plan Name:
2. Step 1:
3. Step 2:
4. Step 3:
5. Agreement Promises (2-3):
```

---

#### Step 2.5: Element 5 - CALL TO ACTION (Direct + Transitional)

**Duration:** 5 minutes

**Principle Reference:**
> "Customers do not take action unless they are challenged to take action."
> — StoryBrand Principle Five

**Actions:**
```yaml
define_cta:
  objective: "Create bold Direct CTA and valuable Transitional CTA"

  direct_cta:
    definition: "Ask for the sale directly"
    analogy: "This is the 'Marry Me' - asking for commitment"
    rules:
      - Clear, bold, specific
      - Single action
      - Visually prominent
      - Use action verbs
      - Don't be apologetic
    weak_examples:
      - "Contact us"
      - "Learn more"
      - "Submit"
      - "Click here"
    strong_examples:
      - "Schedule Your Free Consultation"
      - "Get Started Today"
      - "Book Your Session Now"
      - "Claim Your Spot"
      - "Start Your Free Trial"
    formula: "[Action Verb] + [Specific Outcome]"

  transitional_cta:
    definition: "Capture leads not ready to buy"
    analogy: "This is 'Date Me' - building relationship first"
    purpose:
      - Low commitment
      - Offers value for contact info
      - Positions you as guide
      - Builds trust over time
    types:
      - "PDF/Guide/Checklist"
      - "Video Series"
      - "Webinar"
      - "Quiz/Assessment"
      - "Free Trial"
      - "Email Course"
    formula: "[Get/Download] + [Valuable Resource]"
    examples:
      - "Download Our Free Retirement Checklist"
      - "Watch Our Free Video Series"
      - "Take Our 5-Minute Assessment"
      - "Get Your Free Guide"

  key_insight: |
    You need BOTH types:
    - Direct CTA = For people ready to buy NOW
    - Transitional CTA = For people who need more time

  output_format: |
    CALLS TO ACTION:
    Direct CTA: [Bold request for primary action]
    Transitional CTA: [Valuable offer for email capture]
```

**Elicit:** True

**Interaction Format:**
```
## ELEMENT 5: CALL TO ACTION (Direct + Transitional)

You need TWO types of calls to action. Think of it as "Marry Me" and "Date Me."

### DIRECT CTA ("Marry Me")

This is your primary ask - what action do you want customers to take?

Rules:
- Be bold and specific
- Use action verbs (Schedule, Get, Start, Book, Claim)
- Don't be apologetic

Weak: "Contact us" | "Learn more"
Strong: "Schedule Your Free Consultation" | "Get Started Today"

Formula: [Action Verb] + [Specific Outcome]

**Question:** What is your Direct CTA?

---

### TRANSITIONAL CTA ("Date Me")

For people not ready to buy, what can you offer in exchange for their email?

Types:
- PDF/Guide/Checklist
- Video series
- Webinar
- Quiz/Assessment
- Free trial
- Email course

The key: It must provide REAL VALUE related to their problem.

Formula: [Get/Download] + [Valuable Resource]

Examples:
- "Download Our Free Retirement Planning Checklist"
- "Take Our 5-Minute Financial Health Assessment"
- "Watch Our Free 3-Part Video Series"

**Question:** What valuable resource can you offer as a Transitional CTA?

**Please provide:**
1. Direct CTA:
2. Transitional CTA (and briefly describe what it is):
```

---

#### Step 2.6: Element 6 - FAILURE (Stakes)

**Duration:** 5 minutes

**Principle Reference:**
> "Every human being is trying to avoid a tragic ending."
> — StoryBrand Principle Six

**Actions:**
```yaml
define_failure:
  objective: "Articulate what customer stands to lose if they don't act"

  psychology: |
    LOSS AVERSION: People hate losing something MORE than they like gaining something.
    Without stakes, there's no urgency. Without urgency, there's no action.

  stake_categories:
    financial: "Money lost or opportunities missed"
    time: "Time wasted that they'll never get back"
    opportunity: "Chances they'll miss out on"
    quality_of_life: "How daily life will suffer"
    relationships: "Impact on family, team, connections"
    health: "Physical or mental health consequences"
    status: "Reputation or position affected"

  questions:
    - "What will happen if they DON'T solve this problem?"
    - "What will they lose or miss out on?"
    - "What gets worse if they do nothing?"
    - "What's at risk?"

  balance_rule: |
    DO: Mention stakes 2-3 times, make them real and relevant
    DON'T: Overdo it, use scare tactics, make exaggerated claims

  examples:
    financial_advisor:
      - "Without a plan, you might outlive your money"
      - "You could miss the retirement you've worked for"
      - "Your family might face financial stress"
    it_services:
      - "System failure could cost thousands in lost productivity"
      - "Data breach could destroy customer trust"
      - "Keep wasting time on problems that should be solved"
    coach:
      - "Continue feeling stuck and frustrated"
      - "Miss opportunities that pass you by"
      - "Watch others succeed while you stay the same"

  output_format: |
    FAILURE (Stakes):
    - [What they lose/risk 1]
    - [What they lose/risk 2]
    - [What they lose/risk 3]
```

**Elicit:** True

**Interaction Format:**
```
## ELEMENT 6: FAILURE (Stakes)

Now we need to communicate what's at RISK. This creates urgency.

> "People hate losing something more than they like winning something."

This isn't about fear-mongering - it's about being honest about the consequences of inaction.

### Questions to Consider:
- What happens if they DON'T solve this problem?
- What will they lose or miss out on?
- What gets worse over time?
- What's truly at stake?

### Categories of Stakes:
- Financial: Money lost, opportunities missed
- Time: Wasted time never recovered
- Quality of Life: Daily life suffering
- Relationships: Family, team affected
- Health: Physical or mental impact
- Status: Reputation or position

### Examples (Financial Advisor):
- "Without a plan, you might outlive your money"
- "You could miss the retirement you've worked your whole life for"
- "Your family might face unnecessary financial stress"

**Question:** What 2-3 things does your customer stand to LOSE if they don't act?

**Please provide:**
1. Stake 1:
2. Stake 2:
3. Stake 3:
```

---

#### Step 2.7: Element 7 - SUCCESS (Transformation)

**Duration:** 5-7 minutes

**Principle Reference:**
> "Never assume people understand how your brand can change their lives. Tell them."
> — StoryBrand Principle Seven

**Actions:**
```yaml
define_success:
  objective: "Paint vivid picture of success at three levels"

  three_dimensions:
    external_success:
      definition: "Tangible, observable outcomes"
      questions:
        - "What measurable results will they achieve?"
        - "What will change in their external world?"
        - "What will others see?"
      examples:
        - "Secure retirement with income you can count on"
        - "Technology that works without constant problems"
        - "Business growing 20% year over year"

    internal_success:
      definition: "How they will FEEL after"
      questions:
        - "What emotions will they experience?"
        - "What internal struggles will be resolved?"
        - "How will their self-perception change?"
      common_feelings:
        - Confident
        - Peaceful
        - Proud
        - Relieved
        - Empowered
        - Free
        - Secure
      examples:
        - "Feel confident about your financial future"
        - "Experience peace of mind knowing you're on track"
        - "Feel proud of what you've built"

    aspirational_identity:
      definition: "Who they will BECOME"
      key_insight: "This is the most important part of the framework"
      questions:
        - "Who does your customer want to become?"
        - "What identity are they aspiring to?"
        - "How will this transform who they are?"
      transformations:
        - "Overwhelmed beginner -> Confident expert"
        - "Stressed executive -> Peaceful leader"
        - "Worried parent -> Confident provider"
        - "Amateur -> Professional"
        - "Struggling -> Thriving"
      formula: "From [current identity] to [aspirational identity]"

  identity_transformation: |
    The complete arc:
    BEFORE: [Who they are now - struggling]
    AFTER: [Who they become - transformed]

    Example (Luke Skywalker):
    Before: Lonely, insecure farm boy
    After: Confident Jedi Knight

  output_format: |
    SUCCESS:
    External (tangible outcomes):
    - [Result 1]
    - [Result 2]

    Internal (how they'll feel):
    - [Feeling 1]
    - [Feeling 2]

    Identity Transformation:
    From: [Who they are now]
    To: [Who they become]

    Aspirational Identity: [The identity they aspire to]
```

**Elicit:** True

**Interaction Format:**
```
## ELEMENT 7: SUCCESS (Transformation)

This is your happy ending. Paint a vivid picture of life AFTER they work with you.

> "Never assume people understand how your brand can change their lives. Tell them."

We need THREE dimensions of success:

### EXTERNAL SUCCESS
What tangible, measurable outcomes will they experience?

Example: "Secure retirement with reliable income"

**Question:** What external results will they see?

---

### INTERNAL SUCCESS
How will they FEEL after working with you?

Common feelings: Confident, Peaceful, Proud, Relieved, Empowered, Free, Secure

Example: "Feel confident and at peace about your financial future"

**Question:** How will they feel emotionally?

---

### IDENTITY TRANSFORMATION
This is the most important part. Who will they BECOME?

Formula: From [current identity] → To [aspirational identity]

Example:
- Before: Anxious person uncertain about retirement
- After: Confident retiree enjoying financial freedom

Aspirational identities: Confident leader, Peaceful executive, Thriving business owner, Expert in their field

**Question:** What identity transformation will they experience?

**Please provide:**
1. External Success (2 tangible outcomes):
2. Internal Success (how they'll feel):
3. Identity Transformation (from → to):
4. Aspirational Identity (one phrase describing who they become):
```

---

### PHASE 3: COMPILATION & OUTPUT

#### Step 3.1: Compile BrandScript

**Duration:** 5 minutes

**Actions:**
```yaml
compile_brandscript:
  objective: "Assemble all elements into complete BrandScript"

  format: |
    # [BUSINESS NAME] BRANDSCRIPT

    ## CHARACTER
    **Who:** [Customer description]
    **Wants:** [Primary desire]

    ## PROBLEM
    **Villain:** [Root cause]
    **External:** [Tangible problem]
    **Internal:** [How it makes them feel]
    **Philosophical:** [Why it matters]

    ## GUIDE
    **Empathy:** [Understanding statement]
    **Authority:** [Proof of competence]

    ## PLAN
    **Name:** [Plan name]
    1. [Step 1]
    2. [Step 2]
    3. [Step 3]

    **Agreement:** [Key promises]

    ## CALL TO ACTION
    **Direct:** [Primary CTA]
    **Transitional:** [Lead magnet offer]

    ## FAILURE
    - [Stake 1]
    - [Stake 2]
    - [Stake 3]

    ## SUCCESS
    **External:** [Tangible outcomes]
    **Internal:** [How they'll feel]
    **Transformation:** [From → To]
    **Aspirational Identity:** [Who they become]

  narrative_format: |
    At [COMPANY] we know that you want to be a [IDENTITY TRANSFORMATION].

    In order to do that, you need [CHARACTER WANT].

    The problem is [EXTERNAL PROBLEM], which makes you feel [INTERNAL PROBLEM].

    We believe [PHILOSOPHICAL PROBLEM].

    We understand [EMPATHY], which is why we [AUTHORITY].

    Here's how we do it:
    1. [STEP 1]
    2. [STEP 2]
    3. [STEP 3]

    So, [DIRECT CTA].

    And in the meantime, [TRANSITIONAL CTA].

    So you can stop [FAILURE] and instead [SUCCESS].
```

---

#### Step 3.2: Create One-Liner

**Duration:** 3 minutes

**Actions:**
```yaml
create_one_liner:
  objective: "Create concise one-liner using Problem + Solution + Success"

  formula: |
    [Identify the problem] + [Introduce your solution] + [Describe the success]

  template: |
    [Problem statement - what challenge do customers face?]
    [Solution statement - how you solve it]
    [Success statement - what they'll experience]

  examples:
    financial_advisor: |
      "Most people approaching retirement don't know if they'll have enough money.
      We create personalized retirement plans that give you confidence.
      So you can enjoy the retirement you've worked your whole life for."

    it_services: |
      "Technology problems cost businesses thousands in lost productivity.
      We provide reliable IT support with same-day response.
      So you can focus on your business, not your computers."

    fitness_coach: |
      "Most busy professionals struggle to stay healthy with their demanding schedules.
      We provide personalized fitness plans that fit your lifestyle.
      So you can feel energized and confident every day."

  usage_locations:
    - Website footer
    - Email signature
    - Social media bios
    - Business cards
    - Networking/elevator pitch
    - About page
```

---

#### Step 3.3: Implementation Guidance

**Duration:** 5 minutes

**Actions:**
```yaml
provide_implementation:
  objective: "Give practical guidance for applying BrandScript"

  website_header:
    components:
      - Headline (benefit-focused)
      - Subheadline (clarification)
      - Direct CTA button
      - Success image
    template: |
      Headline: [Primary benefit - what they GET]
      Subheadline: [Brief clarification of how]
      CTA: [Direct CTA button]

  value_proposition:
    format: "3-4 bullet points of key benefits"
    focus: "What they GET, not what you DO"

  email_subjects:
    nurture_examples:
      - "[Solve Problem] in [Time Frame]"
      - "The #1 mistake [audience] makes with [topic]"
      - "How [desired outcome] without [pain point]"
    sales_examples:
      - "Ready to [achieve goal]?"
      - "[Time-sensitive] opportunity for [outcome]"
      - "Your [solution] is waiting"

  application_checklist:
    - "Website homepage header"
    - "About page"
    - "Email welcome sequence"
    - "Sales presentations"
    - "Social media bios"
    - "Business cards"
    - "Elevator pitch"
    - "Team training"
```

---

### PHASE 4: DELIVERY & VALIDATION

#### Step 4.1: Deliver Complete Output

**Duration:** 5 minutes

**Output Format:**
```markdown
# COMPLETE BRANDSCRIPT: [BUSINESS NAME]

---

## BRANDSCRIPT GRID

| Element | Content |
|---------|---------|
| **Character** | [Who] wants [Want] |
| **Problem** | External: [X], Internal: [X], Philosophical: [X] |
| **Guide** | Empathy: [X], Authority: [X] |
| **Plan** | 1. [X] 2. [X] 3. [X] |
| **CTA** | Direct: [X], Transitional: [X] |
| **Failure** | [Stakes] |
| **Success** | [External + Internal + Transformation] |

---

## NARRATIVE BRANDSCRIPT

[Complete narrative paragraph format]

---

## ONE-LINER

[Complete one-liner]

---

## IMPLEMENTATION READY COPY

### Website Header
**Headline:** [X]
**Subheadline:** [X]
**CTA Button:** [X]

### Value Proposition Bullets
- [Benefit 1]
- [Benefit 2]
- [Benefit 3]

### Email Subject Lines
1. [Subject 1]
2. [Subject 2]
3. [Subject 3]

---

## VALIDATION CHECKLIST

- [ ] Customer is positioned as hero
- [ ] Problem defined at all 3 levels
- [ ] Empathy + Authority both present
- [ ] Plan is 3 steps
- [ ] Both CTAs are clear
- [ ] Stakes create urgency
- [ ] Success includes transformation
- [ ] Message passes "grunt test"

---

## NEXT STEPS

1. Apply to website homepage
2. Update email signature with one-liner
3. Train team on messaging
4. Create transitional CTA content
5. Review all marketing materials for consistency
```

---

#### Step 4.2: Validate with Grunt Test

**Duration:** 2 minutes

**Actions:**
```yaml
validate_output:
  grunt_test:
    definition: "Could a caveman understand what you offer in 5 seconds?"
    questions:
      - "What do you offer?"
      - "How will it make my life better?"
      - "What do I need to do to buy it?"

  checklist:
    - customer_is_hero: "Brand positioned as guide, not hero"
    - problem_complete: "All 3 levels addressed"
    - guide_balanced: "Both empathy AND authority present"
    - plan_simple: "3 steps or fewer"
    - ctas_clear: "Direct and transitional CTAs defined"
    - stakes_present: "Failure consequences articulated"
    - success_vivid: "Transformation clearly described"
    - clarity: "Simple, clear language throughout"
```

---

## Error Handling

### Incomplete Information

| Issue | Resolution |
|-------|------------|
| Vague customer description | Probe for specifics: demographics, situation, needs |
| Can't identify internal problem | Offer feeling options: frustrated, overwhelmed, anxious, etc. |
| No clear authority | Ask about experience, results, testimonials, credentials |
| Plan too complex | Help simplify to 3 core steps |
| Weak CTA | Provide strong CTA examples and formula |

### Common Corrections

| Mistake | Correction |
|---------|------------|
| Brand as hero | Reframe all copy from customer perspective |
| Features vs benefits | Translate features into customer outcomes |
| Multiple wants | Focus on ONE primary desire |
| Vague stakes | Make consequences specific and real |
| Generic success | Add emotional and transformation elements |

---

## Quality Standards

### BrandScript Quality Checklist

- [ ] **Character:** One clear, specific want identified
- [ ] **Problem:** All 3 levels (external, internal, philosophical) defined
- [ ] **Guide:** Both empathy AND authority present
- [ ] **Plan:** Exactly 3 clear steps
- [ ] **CTA:** Both direct and transitional CTAs defined
- [ ] **Failure:** 2-3 specific stakes articulated
- [ ] **Success:** External, internal, AND transformation included
- [ ] **Clarity:** Passes the "grunt test"
- [ ] **Consistency:** All elements work together
- [ ] **Actionable:** Ready to implement immediately

### One-Liner Quality

- [ ] Follows Problem + Solution + Success formula
- [ ] 2-4 sentences maximum
- [ ] Clear and memorable
- [ ] Can be spoken naturally
- [ ] Addresses customer's problem first

---

## Examples

### Example 1: Financial Advisor BrandScript

```
CHARACTER:
Who: Professionals 45-60 approaching retirement
Wants: Financial security and freedom to enjoy retirement

PROBLEM:
Villain: Conflicting financial advice
External: Don't know if they have enough saved
Internal: Feel anxious and uncertain about the future
Philosophical: Everyone deserves to enjoy the retirement they've worked for

GUIDE:
Empathy: "We know how overwhelming it feels to plan for retirement with so many unknowns."
Authority: "For 20 years, we've helped over 500 families retire with confidence."

PLAN: The Retirement Clarity Process
1. Schedule your free discovery call
2. We create your personalized retirement roadmap
3. Watch your wealth grow with confidence

CTA:
Direct: "Schedule Your Free Discovery Call"
Transitional: "Download Our Free 'Am I Ready to Retire?' Checklist"

FAILURE:
- Outlive your money
- Miss the retirement you've worked for
- Burden your family with financial stress

SUCCESS:
External: Secure retirement income, clear financial plan
Internal: Feel confident and at peace about your future
Transformation: From anxious saver → confident retiree
Aspirational Identity: Someone who enjoys what they've earned

ONE-LINER:
"Most people approaching retirement don't know if they'll have enough money.
We create personalized retirement plans that give you confidence.
So you can enjoy the retirement you've worked your whole life for."
```

### Example 2: IT Services BrandScript

```
CHARACTER:
Who: Small business owners with 10-50 employees
Wants: Technology that works without constant headaches

PROBLEM:
Villain: Complexity and unreliable systems
External: Computers crash, systems are slow, security is uncertain
Internal: Frustrated, embarrassed when tech fails in front of clients
Philosophical: Technology should make business easier, not harder

GUIDE:
Empathy: "We understand the frustration of technology that's supposed to help but ends up wasting your time."
Authority: "Certified by Microsoft, we've supported 200+ businesses with 99.9% uptime."

PLAN: The Stress-Free Tech Plan
1. Book your free technology audit
2. We implement your custom solution
3. Enjoy reliable technology with 24/7 support

CTA:
Direct: "Book Your Free Tech Audit"
Transitional: "Download Our Cybersecurity Checklist"

FAILURE:
- System failure costs thousands in lost productivity
- Data breach destroys customer trust
- Continue wasting time on problems that should be solved

SUCCESS:
External: Systems that work, fast support, secure data
Internal: Feel confident and in control of technology
Transformation: From tech-frustrated → tech-empowered
Aspirational Identity: Modern business running on reliable systems

ONE-LINER:
"Technology problems cost businesses thousands in lost productivity.
We provide reliable IT support with same-day response.
So you can focus on your business, not your computers."
```

---

## Related Resources

- **Agent:** @donald-miller
- **Research:** squads/storytelling/research/donald-miller-storybrand-research.md
- **Template:** templates/brandscript-template.yaml
- **Checklist:** checklists/message-clarity-checklist.md

---

**Task Version:** 1.0.0
**Created:** 2026-01-30
**Author:** AIOX Squad Architect
**Methodology Source:** Donald Miller, Building a StoryBrand
