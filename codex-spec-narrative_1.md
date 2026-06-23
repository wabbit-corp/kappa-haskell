# Codex: A Diegetic Knowledge System

## 1. Introduction

The Codex is a game system where knowledge is earned through play. Unlike traditional game UIs that omnisciently display item stats and creature health bars, the Codex represents what the *character* knows — learned through eating plants, fighting creatures, talking to other players, and reading discovered texts.

Knowledge in the Codex has three essential properties:

1. **Attribution** — You only learn what you can causally attribute. Eating a lone mushroom teaches you about that mushroom. Eating a stew with five ingredients teaches you about the stew as a composite dish, not its individual components.

2. **Accumulation** — Learning is progressive. Seeing a creature once tells you it's hostile. Killing ten of them gives you a rough sense of their health. Killing fifty with varied weapons reveals their weaknesses.

3. **Provenance** — Every fact remembers where it came from. Did you experience this yourself? Did someone tell you? Did you read it in a book? The Codex tracks this, and it matters — because people can lie.

---

## 2. What Players See

When a player opens their Codex and looks up an entity, they see a journal-style entry combining structured facts, prose passages, and their own notes.

### 2.1 A Sample Entry

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  MOONPETAL MUSHROOM
  Alias: "Death Cap" (my name for it)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  [Small sketch of the mushroom]

  PROPERTIES
  ──────────────────────────────────────────────────────
  ✓ Toxic: Yes
  ✓ Lethality: Fatal
    Habitat: Mistwood Vale, Shadow Glen
    Culinary: (unknown)
    Medicinal: (unknown)

  JOURNAL
  ──────────────────────────────────────────────────────
  Day 23 — First encountered near the old mill in 
  Mistwood Vale.

  Day 24 — I ate one of these while foraging. I did 
  not survive the experience. Extremely dangerous.

  NOTES
  ──────────────────────────────────────────────────────
  Thornwood claims these can be used in antidotes if
  prepared correctly, but I don't trust him after the
  incident with the berries.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  First encountered: Day 23
  [Add Note] [Transcribe to Paper] [Set Alias]
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

The checkmarks (✓) indicate self-verified facts — things the player learned through direct experience. Facts without checkmarks came from other sources (other players, books, NPCs) and display their attribution.

### 2.2 Progressive Disclosure

Properties don't reveal fully at once. The Codex shows different levels of detail based on how much the player has learned:

| Confidence | Display |
|------------|---------|
| Low (< 0.3) | "(unknown)" |
| Vague (0.3 - 0.6) | "Seems fairly tough" |
| Approximate (0.6 - 0.9) | "Takes about 50 damage to kill" |
| Known (> 0.9) | "Has 47 health" |

Different properties require different amounts of evidence:

- **Hostile**: One observation (if it attacks you, you know)
- **Approximate health**: 3-5 kills with consistent damage
- **Precise health**: 10+ kills with low variance in damage dealt
- **Weakness**: 8+ kills using varied damage types
- **Behavior patterns**: 15+ extended observations

### 2.3 Conflicts

When the player has conflicting information, the Codex shows all versions with their sources:

```
  ⚠️ CONFLICTING INFORMATION

  Toxic:
    ✓ Yes (I ate one and died)
    No — From: "Herbalist's Guide" by Thornwood
         [Strike out]
```

The player can strike out facts they believe to be false. Struck-out facts are hidden but not deleted — they can be restored later. Self-verified facts cannot be struck out; you can't deny your own experience.

---

## 3. How Knowledge Is Acquired

### 3.1 Direct Experience

The primary way to learn is by doing. The game engine emits events, and the Codex system evaluates rules against those events to determine what the player learns.

**Consumption events** teach about plants and food:
- Eating a mushroom and dying → learn it's toxic/fatal
- Eating a mushroom and getting sick → learn it's toxic/dangerous
- Eating a mushroom with no ill effects (after waiting) → learn it's probably safe

**Combat events** teach about creatures:
- Being attacked → learn the creature is hostile
- Killing creatures → accumulate health estimates
- Getting poisoned during combat → learn the creature is venomous
- Dying to a creature → strong evidence of danger

**Discovery events** teach basics:
- First encounter → mark "first seen" date and location
- Harvesting → learn the plant's name
- Looting → learn creature drops

### 3.2 The Attribution Requirement

Learning requires *causal isolation*. If you eat a mushroom alone and die, you know the mushroom killed you. But if you eat a stew containing five ingredients and die, you only learn that the stew is deadly — not which ingredient caused it.

The system tracks a "causal window" around events. If multiple potential causes exist within that window, no individual attribution is possible.

This creates interesting gameplay: a clever poisoner might mix a deadly mushroom into a multi-ingredient dish, knowing the victim won't learn which component killed them.

### 3.3 Social Learning

Players can tell each other things. When one player says "that mushroom is deadly" to another, the system extracts the claim and offers to add it to the listener's Codex.

**The extraction pipeline:**

1. **Pre-filter** — Most chat messages aren't knowledge claims. The system uses pattern matching to identify likely claims:
   - "X is Y" / "X are Y"
   - "don't eat X" / "X will kill you"  
   - "I'm [name]" / "call me [name]"
   - References to held/nearby objects ("that mushroom")

2. **Entity resolution** — The system resolves references using game context:
   - "that" / "this" → the held item or nearest entity
   - "self" / "I" → the speaker
   - "you" → the listener
   - Named entities matched against visible entities

3. **LLM fallback** — Complex or ambiguous claims go to an LLM for extraction

4. **Confirmation** — A subtle toast appears: "📖 Thornwood says the mushroom is deadly. [Add to Codex] [Dismiss]"

**No special syntax required.** Players speak naturally. The system does its best to extract meaning, and fails gracefully when it can't.

### 3.4 Reading Documents

In-game books, scrolls, and papers contain knowledge that transfers to the reader's Codex. When a player reads a document:

1. The system parses the document's claims
2. For each entity mentioned, relevant facts are added to the reader's Codex
3. Attribution shows the document as source: "From: 'Herbalist's Guide' by Thornwood"

Canonical sources (official game lore, NPC scholars, ancient inscriptions) carry higher credibility than player-written documents.

---

## 4. Credibility and Lying

### 4.1 The Credibility Model

The Codex tracks where every fact came from. But unlike internal confidence scores, the *display* to players is deliberately simple. There are only three visible states:

| Display | Meaning |
|---------|---------|
| ✓ (checkmark) | **Self-verified** — I experienced this directly |
| "From [Source]" | **Attributed** — Someone or something told me |
| ✎ (quill icon) | **Self-authored** — I wrote this myself |

No tier numbers. No "reliability ratings." Just: did you see it yourself, who told you, or did you write it.

### 4.2 Why This Enables Lying

If the Codex showed credibility tiers (e.g., "Tier 1: Witnessed, Tier 3: Hearsay"), players could use the UI to detect lies. "You said you witnessed this, but your Codex shows it as Tier 3 hearsay — you're lying!"

By hiding internal credibility mechanics, we preserve the possibility of deception. When someone tells you a fact, you don't know if they experienced it themselves or are making it up. You have to decide whether to trust them based on your relationship, their reputation, and how plausible the claim is.

### 4.3 The Lying Workflow

Here's how a player might deceive another:

1. **Truth in Codex**: The player knows Moonpetal is deadly (self-verified from dying to it)

2. **Strike out the truth**: The player hides the true fact (it's not deleted, just hidden from view)

3. **Write a false fact**: Using the "Add Note" or "Write Fact" feature, the player creates a self-authored claim: "Edible: Yes, quite tasty"

4. **Transcribe to paper**: The player transcribes their Codex entry to a physical paper item. Only non-hidden facts are copied.

5. **Give to victim**: The victim receives a paper that says "Moonpetal — Edible: Yes, quite tasty — Written by Thornwood"

The victim sees attributed information. They don't know Thornwood struck out his real knowledge and fabricated this claim. If they eat the mushroom and die, their Codex updates with the truth, and now they see the conflict — and know who lied to them.

### 4.4 Constraints on Lying

Some limits prevent the system from being too abusable:

- **Self-verified facts cannot be struck out.** You can't hide what you actually experienced.
- **Attribution is permanent.** If you write something, your name is attached forever.
- **Self-verification is distinct.** A self-authored fact displays differently from a self-verified one — the quill icon vs. the checkmark.

Reputation becomes valuable. A player known for accurate information can trade that trust for influence or currency. A player caught lying loses credibility the hard way — through the social network, not the UI.

---

## 5. Knowledge Transfer

### 5.1 Transcription

Players can transcribe Codex entries to physical items (papers, pages) that exist in the game world. This requires materials — ink, quill, and paper — and produces a tradeable object.

When transcribing, the player chooses what to include:
- Which properties
- Which journal entries
- Whether to include personal notes

Only non-hidden facts are transcribed. Hidden (struck-out) facts are omitted.

### 5.2 Books

Multiple pages can be bound into a book. A book has:
- A title
- An optional preface/description
- Ordered pages
- Compiler attribution

Books can be copied (if you have the materials), creating a new physical item with the same contents.

### 5.3 Import Behavior

When a player reads a document they don't already have in their Codex, they can choose how to import the knowledge:

- **Add All**: Import everything. May create conflicts with existing knowledge.
- **Fill Gaps**: Only add facts for properties you don't already know.
- **Add as Rumor**: Import everything, but with low confidence (0.3). Useful for information you don't fully trust.
- **Interactive**: Review each fact and decide individually.

### 5.4 Credibility Propagation

When knowledge is transcribed and transferred, credibility degrades:

| Original Source | After Transfer |
|-----------------|----------------|
| Self-verified | From [Transcriber] (attested) |
| Canonical (game lore) | Canonical (preserved) |
| From [Player A] | From [Player A] via [Transcriber] (reported) |
| Self-authored | From [Author] (claimed) |

The chain of custody is preserved. If Alice tells Bob a fact, and Bob transcribes it for Carol, Carol sees: "From Alice, via Bob."

### 5.5 Maps

Location knowledge can be transcribed to maps. A map segment contains:
- Named locations within a radius
- Known resources at each location
- Danger levels
- Creature sightings

Maps are valuable trade goods. A player who has thoroughly explored a dangerous region can sell their map knowledge to others.

---

## 6. The Event System

### 6.1 Event Structure

Game events are predicates with named argument roles:

```
(ate :subject player-17 
     :object mushroom-42
     :when 1703847293 
     :where mistwood-vale 
     :witnesses ())

(killed :subject player-17 
        :object boar-89
        :weapon iron-sword-3 
        :damage-dealt 47
        :when 1703847310 
        :where mistwood-vale
        :witnesses (player-23 player-41))

(said :subject player-23 
      :content "that mushroom is deadly"
      :addressing player-17 
      :referencing (mushroom-42)
      :when 1703847295 
      :where mistwood-vale
      :witnesses (player-17))
```

### 6.2 Existential Quantification

When querying events, unspecified arguments are existentially quantified. The query "did player-17 eat mushroom-42?" becomes:

```
(exists (?when ?where ?witnesses)
  (ate :subject player-17 
       :object mushroom-42
       :when ?when 
       :where ?where 
       :witnesses ?witnesses))
```

This allows rules to match events without caring about every detail.

### 6.3 Event Types

The system handles these event categories:

**Consumption**: `ate`, `drank`, `consumed-in-recipe`

**Combat**: `attacked`, `killed`, `damaged-by`, `received-effect`, `died`, `combat-started`, `combat-ended`

**Discovery**: `found`, `observed`, `harvested`, `looted`, `inspected`

**Social**: `heard`, `read`, `witnessed`, `told-by-npc`

**Crafting**: `crafted`, `failed-craft`, `experimented`

**World**: `visited`, `entered-region`, `triggered-world-event`

---

## 7. The Two-Tier Fact Store

### 7.1 The Problem

A naive implementation would store every event forever and query them when needed. This doesn't scale — after hours of play, the event log becomes enormous, and rule evaluation becomes slow.

But we can't just discard events immediately either. Learning rules need to correlate events across time:
- "You ate X, and then within 30 seconds you died" → learn X is deadly
- "You fought creatures A and B, and got poisoned, but you've fought A alone before without getting poisoned" → learn B is venomous

### 7.2 The Solution: Hot and Cold Tiers

**Hot Tier** (10-minute sliding window):
- Stores all recent events
- Fully indexed by subject, object, event type, location
- Supports fast first-order logic queries
- Events evicted when they fall outside the window

**Cold Tier** (persistent storage):
- Stores learned facts with confidence and provenance
- Stores historical events (only notable ones)
- Stores aggregate counts (kills, harvests, visits)
- Queryable but not as flexible as hot tier

### 7.3 Compaction: What Survives Eviction?

When an event is evicted from the hot tier, the system decides whether to preserve it:

1. **Did it trigger learning?** If a rule fired and produced facts, those facts are now in the cold tier. The raw event can be discarded.

2. **Is it a first occurrence?** The first time you see a creature type, that's worth remembering. Preserve it.

3. **Does it involve notable entities?** Events involving famous players, legendary items, or important locations get preserved.

4. **Are there multiple witnesses?** Events seen by several players are more likely to be historically significant.

5. **Is it a player interaction?** Social events (conversations, trades) are preserved for the social graph.

6. **Did the player explicitly mark it?** Players can flag events as notable.

Everything else is discarded. The cold tier stores what matters; the hot tier handles ephemeral event correlation.

### 7.4 Aggregates

Some learning rules need counts that would be expensive to compute from raw events:
- "Has this player killed more than 10 boars?"
- "What's the variance in damage dealt to this creature type?"

The system maintains running aggregates that update incrementally with each event:
- **Counts**: kill counts, harvest counts, visit counts
- **Sums**: total damage dealt, total gold earned
- **Variance**: running Welford's algorithm for damage variance

This allows rules to check "has the player killed enough of these to learn their health?" without scanning all historical events.

---

## 8. The Rule Engine

### 8.1 Rule Structure

A learning rule has three parts:

1. **Trigger**: An event pattern that activates the rule
2. **Conditions**: Predicates that must hold for the rule to fire
3. **Effects**: Actions taken when the rule fires

### 8.2 Rule Syntax

Rules are written in a Lisp-like DSL:

```clojure
(defrule "learn-toxicity-from-death"
  :trigger (ate :subject ?self :object ?item)
  :conditions 
    [(self? ?self)
     (isolated ?item ?t1)
     (exists (died :subject ?self :when ?t2)
             (immediate ?t1 ?t2))]
  :effects
    [(learn! ?item :toxic true :confidence 0.95)
     (learn! ?item :lethality :deadly)
     (journal! ?item "consumption_death")])
```

This rule says: "When I eat something, and I'm the only one who ate it recently, and I die immediately afterward, learn that it's toxic and fatal, and add a journal entry."

### 8.3 Condition Types

**Identity checks:**
- `(self? ?x)` — Is this variable the current player?

**Causal isolation:**
- `(isolated ?entity ?time)` — Was this the only consumption in the causal window?

**Event existence:**
- `(exists (pattern) ...)` — Does a matching event exist in the hot tier?
- `(not-exists (pattern))` — Ensure no such event exists

**Knowledge queries:**
- `(knows ?entity ?property)` — Do I know this property?
- `(knows ?entity ?property :confidence 0.5)` — With at least this confidence?
- `(not-knows ?entity ?property)` — I don't know this yet

**Aggregate checks:**
- `(count (killed :subject ?self :object-type ?type) (>= 3))` — At least 3 kills
- `(variance-below (killed ...) :damage-dealt 0.2)` — Low variance in damage

**Time predicates:**
- `(immediate ?t1 ?t2)` — Events within a few game ticks
- `(within ?t1 ?t2 300)` — Within 300 ticks
- `(after ?t1 ?t2 1000)` — At least 1000 ticks apart

**Combinators:**
- `(and ...)`, `(or ...)`, `(not ...)`

### 8.4 Effect Types

**Learning:**
- `(learn! ?entity ?property ?value)` — Add or update a fact
- `(learn! ?entity ?property ?value :confidence 0.8)` — With explicit confidence

**Journal entries:**
- `(journal! ?entity "template_name")` — Add prose from template
- `(journal! ?entity "template" :param1 ?val1)` — With parameters

**Reveals:**
- `(reveal! ?entity "section_id")` — Mark a prose section as revealed

**Aggregates:**
- `(increment-aggregate! :kill-count ?creature-type)` — Update counters
- `(update-variance! :damage-dealt ?damage)` — Update running variance

**First-seen tracking:**
- `(mark-first-seen! ?entity)` — Record first encounter

### 8.5 Example Rules

**Learn creature health from repeated kills:**

```clojure
(defrule "learn-health-approximate"
  :trigger (killed :subject ?self :object ?creature :damage-dealt ?dmg)
  :conditions 
    [(self? ?self)
     (count (killed :subject ?self :object-type (type-of ?creature)) (>= 3))
     (variance-below (killed :subject ?self :object-type (type-of ?creature)) 
                     :damage-dealt 0.3)]
  :effects
    [(learn! ?creature :health (mean-damage ?creature) :confidence 0.6)])
```

**Infer poison source when fighting multiple creatures:**

```clojure
(defrule "infer-poison-source"
  :trigger (received-effect :subject ?self :effect :poison)
  :conditions 
    [(self? ?self)
     (fighting-count (>= 2))
     (exists (fighting :subject ?self :against ?unknown)
             (not-knows ?self ?unknown :venomous))
     (exists (fighting :subject ?self :against ?known)
             (knows ?self ?known :venomous false :confidence 0.5))]
  :effects
    [(learn! ?unknown :venomous true :confidence 0.7)])
```

This rule fires when you're poisoned while fighting multiple creatures. If you know one isn't venomous (from fighting it alone before), you can infer the other one is.

---

## 9. Confidence Mechanics

### 9.1 The Confidence Model

Each fact has a confidence value between 0 and 1. Confidence increases with evidence using a Bayesian-ish update:

```
new_confidence = old_confidence + k × (1 - old_confidence)
```

Where `k` is the learning rate for that type of evidence. This creates diminishing returns — early observations teach a lot, later observations refine.

### 9.2 Evidence Sources

Different sources provide different confidence deltas:

| Source | Typical Confidence |
|--------|-------------------|
| Direct death from consumption | 0.95 |
| Sickness from consumption | 0.70 |
| No ill effects (delayed check) | 0.60 |
| Killing a creature | 0.15 per kill (accumulates) |
| Being told by another player | 0.50 |
| Reading in a document | 0.60 |
| Canonical game lore | 0.90 |

### 9.3 Reveal Thresholds

Properties have reveal thresholds that determine how they display:

```clojure
(def-reveals :creature
  {:hostile     [[0.5 :known]]       ; Binary, no vague tier
   :venomous    [[0.4 :vague] [0.7 :known]]
   :health      [[0.3 :vague] [0.6 :approximate] [0.9 :known]]
   :weakness    [[0.5 :vague] [0.85 :known]]})
```

At confidence 0.4 for venomous, the player sees "Might be venomous." At 0.7, they see "Venomous: Yes."

### 9.4 Variance Requirements

For numeric properties like health, confidence depends not just on observation count but on variance. If you've killed 10 boars but dealt wildly different damage each time, you don't have a confident health estimate.

The rule engine tracks running variance using Welford's algorithm and includes variance thresholds in conditions:

```clojure
:conditions [(variance-below (killed :subject ?self :object-type boar) 
                             :damage-dealt 0.15)]
```

This ensures the player has consistent data before revealing precise values.

---

## 10. The Rendering Pipeline

### 10.1 Entry Assembly

When the UI requests a Codex entry for an entity:

1. **Gather facts** — Load all facts about this entity from cold tier
2. **Filter hidden** — Remove struck-out facts from primary display
3. **Evaluate reveals** — For each property, determine display tier from confidence
4. **Generate prose** — Apply prose templates with variable substitution
5. **Surface conflicts** — Identify properties with multiple conflicting values
6. **Assemble entry** — Combine structured facts, prose, journal, notes

### 10.2 Prose Templates

Journal entries and flavor text come from templates:

```clojure
{:id "consumption_death"
 :when (knows :toxic)
 :template "I ate this on {date} and did not survive the experience. 
            Extremely dangerous."
 :priority 200}

{:id "health_vague"
 :when (all (confidence>= :health 0.3) (confidence< :health 0.7))
 :template "Seems {health_desc}."
 :priority 60}
```

Templates have reveal conditions and priorities. Multiple matching templates are shown in priority order.

### 10.3 Vague Descriptions

For properties at low confidence, the system generates vague prose rather than showing numbers:

| Health Range | Vague Description |
|--------------|-------------------|
| 0-50 | "fairly fragile" |
| 50-100 | "moderately sturdy" |
| 100-200 | "quite tough" |
| 200-500 | "extremely durable" |
| 500+ | "nearly indestructible" |

This maintains immersion while communicating approximate knowledge.

---

## 11. Integration Contract

The Codex system is game-engine agnostic. The host game implements a hook interface:

### 11.1 Required Hooks

**Event emission:**
```
OnGameEvent(event) — Called when game events occur
```

**Entity resolution:**
```
ResolveEntity(ref) → EntityId — Convert references to IDs
GetEntityType(id) → EntityType — Get the type of an entity
GetEntityName(id) → String — Get display name
```

**Context for NLP:**
```
GetConversationContext(speaker, listener) → Context
  — Returns held items, nearby entities, recent topics
```

**Inventory checks:**
```
CheckInventory(player, items) → Bool 
  — Check if player has required materials
```

**Persistence:**
```
SavePlayerData(player, data) — Persist Codex state
LoadPlayerData(player) → Data — Load Codex state
```

**LLM integration:**
```
ExtractClaims(request) → Claims 
  — Call LLM for complex NLP extraction
```

**UI notifications:**
```
NotifyCodexUpdate(player, update) — Push updates to UI
```

### 11.2 What the Game Provides

The game engine is responsible for:
- Detecting gameplay events and calling `OnGameEvent`
- Maintaining entity state (positions, inventories, etc.)
- Rendering the Codex UI
- Handling physical items (paper, books) in the game world
- Providing LLM access for NLP extraction

### 11.3 What the Codex Provides

The Codex system handles:
- Event indexing and rule evaluation
- Fact storage and confidence tracking
- Knowledge compaction and persistence
- NLP extraction pipeline (pattern matching)
- Prose generation and reveal logic
- Knowledge transfer mechanics

---

## 12. Configuration

All configuration uses EDN (Clojure data literals) syntax.

### 12.1 Schema Configuration

Define entity types and their properties:

```clojure
(defschema :plant
  {:name        {:type :string}
   :edible      {:type :bool}
   :toxic       {:type :bool}
   :lethality   {:type [:enum :values [:harmless :mild :dangerous 
                                       :deadly :instant]]}
   :effects     {:type [:list :of :string]}
   :habitat     {:type [:list :of :string]}})

(defschema :creature
  {:name        {:type :string}
   :hostile     {:type :bool}
   :venomous    {:type :bool}
   :health      {:type :int}
   :drops       {:type [:list :of :string]}
   :weakness    {:type [:list :of :string]}
   :behavior    {:type [:enum :values [:passive :neutral 
                                       :aggressive :territorial]]}})
```

### 12.2 Rule Configuration

Define learning rules:

```clojure
(defrule "learn-toxicity-from-death"
  :trigger (ate :subject ?self :object ?item)
  :conditions [(self? ?self)
               (isolated ?item ?t1)
               (immediate)]
  :effects [(learn! ?item :toxic true :confidence 0.95)
            (learn! ?item :lethality :deadly)
            (journal! ?item "consumption_death")]
  :priority 100)
```

### 12.3 Reveal Configuration

Define property thresholds and prose templates:

```clojure
(def-reveals :creature
  {:hostile  [[0.5 :known]]
   :health   [[0.3 :vague] [0.6 :approximate] [0.9 :known]]
   :weakness [[0.5 :vague] [0.85 :known]]})

(def-prose :creature
  [{:id "killed_by"
    :when (knows :hostile)
    :template "One of these killed me on {date}. Extremely dangerous."
    :priority 200}
   
   {:id "health_vague"
    :when (all (confidence>= :health 0.3) (confidence< :health 0.7))
    :template "Seems {health_desc}."
    :priority 60}])
```

---

## 13. Implementation Notes

### 13.1 Performance Considerations

**Hot tier sizing:** A 10-minute window with ~100 events/minute means ~1,000 events maximum. Indexing keeps query time logarithmic.

**Aggregate updates:** Counters and variances update incrementally with each event (O(1)), not by scanning history (O(n)).

**Cold tier queries:** Fact lookups are by entity ID, then by property — two map lookups. Journal entries are stored per-entity.

### 13.2 Serialization

All types should be serializable without special handling:
- No circular references
- Discriminated unions as tagged objects
- Maps and sets as arrays
- GUIDs as strings

JSON works fine; MessagePack is more compact for persistence.

### 13.3 Concurrency

The hot tier uses mutable state for performance. In a multi-threaded environment:
- Event ingestion should be serialized (single writer)
- Queries can run concurrently (multiple readers)
- Rule evaluation happens synchronously after event ingestion

The cold tier can be safely persisted asynchronously after each rule evaluation completes.

---

## 14. Future Considerations

### 14.1 Notability System

A full implementation might track entity "notability" — how famous or significant an entity is. Notable items used by notable players become more notable themselves. This affects:
- What events get preserved in compaction
- Who gets to name things
- What appears in historical records

### 14.2 Fog of War Maps

The map transfer system could integrate with visual fog of war, where transcribed maps reveal regions on the recipient's world map.

### 14.3 Cross-Server Knowledge

For games with multiple servers or shards, knowledge provenance could track which server information came from, allowing information to flow between worlds while maintaining attribution.

### 14.4 Knowledge Decay

Long-unvisited facts might decay in confidence over time, representing memory fade. "I remember there being something dangerous in those caves, but I can't recall the details..."

---

## 15. Summary

The Codex transforms knowledge from a UI convenience into a gameplay system. Players must earn what they know through experience, trust what others tell them at their own risk, and can trade in information as a valuable commodity.

Key principles:
- **Attribution before learning** — No knowledge without cause
- **Progressive confidence** — Certainty is earned through repetition
- **Provenance tracking** — Every fact remembers its source
- **Lying is possible** — The UI doesn't reveal truth, only claims
- **Knowledge is tradeable** — Transcribe, compile, sell, share

The system is game-agnostic, configured through a Lisp-like DSL, and designed for both single-player depth and multiplayer social dynamics.
