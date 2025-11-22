# Type Systems Course - Capstone Project

## Purpose

Apply everything you've learned by building a complete, working type system of your choice. This project synthesizes knowledge from all 8 chapters and demonstrates mastery.

## Time Estimate

**Minimum**: 20-40 hours (basic project)
**Recommended**: 40-80 hours (comprehensive project)
**Advanced**: 80+ hours (research-level project)

---

## Project Options

Choose ONE project that interests you and matches your skill level.

### Option 1: Mini ML - A Practical Language (Chapters 1-4)

**Goal**: Build a small ML-like language with type inference.

**Requirements**:
- ✅ Lambda calculus foundation (Ch1)
- ✅ Type checking (Ch2)
- ✅ ADTs: products, sums, lists (Ch3)
- ✅ Hindley-Milner type inference (Ch4)
- ✅ Pattern matching on ADTs
- ✅ Let-polymorphism
- ✅ REPL with type display

**Deliverables**:
1. Parser for concrete syntax
2. Type inference implementation
3. Evaluator
4. 20+ test cases
5. Example programs (factorial, map, filter, etc.)
6. Documentation

**Extensions** (optional):
- Type error messages
- Standard library
- Module system

**Skills demonstrated**: Practical type system implementation

---

### Option 2: System F Proof Assistant (Chapters 1-2, 5)

**Goal**: Build a simple proof assistant in System F.

**Requirements**:
- ✅ System F implementation (Ch5)
- ✅ Bi-directional type checking
- ✅ Church encodings for common types
- ✅ Proof construction and verification
- ✅ Parametricity checking

**Deliverables**:
1. System F type checker
2. Church-encoded standard library (Bool, Nat, List, etc.)
3. Proof tactics (simpl, refl, etc.)
4. 10+ verified theorems
5. Tutorial for using the system

**Example Theorems**:
- Parametricity theorems
- List properties (map fusion, etc.)
- Function composition properties

**Skills demonstrated**: Understanding of polymorphism and encoding

---

### Option 3: Verified Vector Library (Chapters 1-2, 7-8)

**Goal**: Implement length-indexed vectors with proofs.

**Requirements**:
- ✅ Dependent types implementation (Ch7-8)
- ✅ Vec type with full API
- ✅ Safe indexing (using Fin)
- ✅ Proved properties

**Deliverables**:
1. Vec implementation
2. Operations: append, reverse, map, zip, etc.
3. Proofs:
   - `length (append xs ys) = length xs + length ys`
   - `reverse (reverse xs) = xs`
   - `map f (map g xs) = map (f . g) xs`
4. Comparison with unsafe lists
5. Documentation

**Skills demonstrated**: Dependent types and theorem proving

---

### Option 4: Type System Comparison Tool (All Chapters)

**Goal**: Implement the SAME language in multiple type systems.

**Requirements**:
- ✅ Define a simple lambda calculus with booleans and naturals
- ✅ Implement in:
  - Untyped (Ch1)
  - Simply typed (Ch2)
  - Hindley-Milner (Ch4)
  - System F (Ch5)
  - Dependent types (Ch7)
- ✅ Compare expressiveness, safety, inference

**Deliverables**:
1. 5 implementations of the same language
2. Example programs in each
3. Comparative analysis:
   - What can each system express?
   - What gets rejected and why?
   - Type annotation burden
4. Formal comparison document
5. Presentation slides

**Skills demonstrated**: Deep understanding of type system tradeoffs

---

### Option 5: Verified Compiler (Chapters 1-8)

**Goal**: Build a compiler with correctness proofs.

**Requirements**:
- ✅ Source language (simply typed LC)
- ✅ Target language (simplified assembly)
- ✅ Compiler implementation
- ✅ Proofs in dependent types:
  - Type preservation
  - Semantic preservation
  - Termination (if applicable)

**Deliverables**:
1. Source language specification
2. Target language specification
3. Compiler implementation
4. Correctness proofs
5. Test suite
6. Documentation

**Skills demonstrated**: Verification of real systems

---

### Option 6: HoTT Explorer (Chapter 8 + Beyond)

**Goal**: Explore Homotopy Type Theory basics.

**Requirements**:
- ✅ Full dependent types with equality (Ch8)
- ✅ Path type instead of Eq
- ✅ Univalence axiom (postulated)
- ✅ Circle type
- ✅ Basic HoTT proofs

**Deliverables**:
1. HoTT implementation (or using Agda/Coq)
2. Path induction
3. Transport and ap functions
4. Example: π₁(S¹) = ℤ (outline)
5. Comparison with ITT
6. Research report

**Skills demonstrated**: Cutting-edge type theory

---

### Option 7: Custom Project (Your Choice!)

**Goal**: Design your own project combining course concepts.

**Requirements**:
- ✅ Use concepts from at least 3 chapters
- ✅ Novel combination or application
- ✅ Clear goals and deliverables
- ✅ Documented design decisions

**Example Ideas**:
- Type system for specific domain (SQL, configs, etc.)
- Effect system (based on types)
- Gradual typing (static + dynamic)
- Linear/affine types
- Refinement types
- Dependent record types

**Approval required**: Discuss with instructor or validate scope yourself

---

## Project Phases

### Phase 1: Planning (1-2 weeks)

- [ ] Choose project
- [ ] Write proposal (1-2 pages)
- [ ] Design architecture
- [ ] Identify key components
- [ ] Create timeline

**Deliverable**: Project proposal

### Phase 2: Core Implementation (3-6 weeks)

- [ ] Implement syntax and AST
- [ ] Implement type checker
- [ ] Implement evaluator
- [ ] Write initial tests
- [ ] Document as you go

**Deliverable**: Working prototype

### Phase 3: Refinement (2-4 weeks)

- [ ] Add missing features
- [ ] Improve error messages
- [ ] Comprehensive testing
- [ ] Performance optimization (if applicable)
- [ ] User documentation

**Deliverable**: Polished implementation

### Phase 4: Evaluation & Presentation (1-2 weeks)

- [ ] Write final report
- [ ] Create examples/demos
- [ ] Prepare presentation
- [ ] Reflect on learning

**Deliverable**: Final report and presentation

---

## Evaluation Criteria

### Technical Implementation (40%)

- **Correctness**: Does it work as specified?
- **Completeness**: Are all requirements met?
- **Code quality**: Is code well-organized and idiomatic?
- **Testing**: Comprehensive test coverage?

### Understanding (30%)

- **Concept application**: Correct use of type theory concepts?
- **Design decisions**: Well-justified choices?
- **Problem solving**: Creative solutions to challenges?

### Documentation (20%)

- **Code comments**: Clear explanation of complex parts?
- **User guide**: Can someone else use it?
- **Technical report**: Explains design and implementation?
- **Examples**: Demonstrates capabilities?

### Presentation (10%)

- **Clarity**: Clear explanation of project?
- **Demos**: Working demonstrations?
- **Reflection**: What did you learn?

---

## Project Template

### Proposal Template

```markdown
# Project Title

## Goal
[One paragraph: what you're building and why]

## Background
[Which chapters/concepts you're using]

## Requirements
- [ ] Requirement 1
- [ ] Requirement 2
...

## Architecture
[High-level design]

## Timeline
- Week 1-2: ...
- Week 3-4: ...
...

## Success Criteria
[How will you know if you succeeded?]

## Risks & Challenges
[What might be difficult?]
```

### Final Report Template

```markdown
# Project Title

## Abstract
[Summary of project]

## Introduction
- Motivation
- Goals
- Approach

## Design
- Architecture
- Key algorithms
- Type system design

## Implementation
- Technologies used
- Key code snippets
- Challenges faced

## Evaluation
- Testing approach
- Results
- Performance (if applicable)

## Examples
- Example 1: ...
- Example 2: ...

## Conclusion
- What worked well
- What was challenging
- What you learned
- Future work

## References

## Appendices
- Full code (or link to repo)
- Additional examples
```

---

## Suggested Timeline

### 8-Week Timeline (Minimal Project)

| Week | Activity |
|------|----------|
| 1 | Planning, proposal |
| 2-3 | Core implementation |
| 4-5 | Features & testing |
| 6 | Documentation |
| 7 | Polish & finalize |
| 8 | Presentation prep |

### 12-Week Timeline (Comprehensive Project)

| Week | Activity |
|------|----------|
| 1-2 | Planning, research, proposal |
| 3-6 | Core implementation |
| 7-9 | Extensions & refinement |
| 10 | Comprehensive testing |
| 11 | Documentation |
| 12 | Final report & presentation |

---

## Resources

### Implementation Help

- Course chapter code as reference
- Haskell libraries: megaparsec, mtl, containers
- Testing: HSpec, QuickCheck
- Documentation: Haddock

### Presentation Help

- Example projects from course exercises
- Research papers (see chapter bibliographies)
- Proof assistant documentation (Agda, Coq, Lean)

---

## Example Projects from Past (Hypothetical)

### "TinyML" by Student A
- Mini ML with HM inference
- 2000 lines of Haskell
- REPL with type display
- Pattern matching on lists
- Grade: Excellent

### "VecLib" by Student B
- Verified vector library in Agda
- 25 proved theorems
- Safe matrix operations
- Comparison with unsafe version
- Grade: Outstanding

### "TypeCmp" by Student C
- Same language in 4 type systems
- Detailed comparative analysis
- 50-page report with examples
- Grade: Excellent

---

## Tips for Success

1. **Start simple**: Get basic version working first
2. **Test early**: Don't wait until the end
3. **Document as you go**: Don't leave it for the end
4. **Ask for help**: Use course resources
5. **Version control**: Use git from day 1
6. **Regular checkpoints**: Review progress weekly
7. **Don't over-scope**: Better to do less well than more poorly

---

## Submission Checklist

- [ ] Source code (well-organized, commented)
- [ ] Tests (comprehensive, passing)
- [ ] User documentation (how to use)
- [ ] Technical report (how it works)
- [ ] Examples (demonstrations)
- [ ] Presentation slides (if presenting)
- [ ] README (overview, build instructions)
- [ ] Reflection (what you learned)

---

## After the Capstone

Congratulations on completing the capstone! You now have:

✅ **Deep understanding** of type systems
✅ **Practical experience** implementing them
✅ **Portfolio piece** for future opportunities
✅ **Foundation** for research or advanced work

### Next Steps:

1. **Share your project**: GitHub, blog post, talk
2. **Contribute**: Open source type systems projects
3. **Specialize**: Choose area for deeper study
4. **Apply**: Use in real projects
5. **Teach**: Help others learn

---

## Questions?

**Scope too large?** → Start with Option 1 (Mini ML)
**Want more challenge?** → Options 5-6
**Unclear what to do?** → Review project requirements
**Need examples?** → See course chapter implementations

**Remember**: The journey matters more than the destination. This project is about consolidating your learning and pushing your understanding further!

Good luck! 🚀

---

*"The best way to learn type systems is to build one." - Course Motto*
