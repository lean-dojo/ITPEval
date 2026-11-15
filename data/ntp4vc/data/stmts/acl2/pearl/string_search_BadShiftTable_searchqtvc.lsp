;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/string_search_BadShiftTable_searchqtvc: the bad-character string
;; search verification condition, preserving the no-earlier-match invariant
;; and establishing the search result specification. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Signed integers in this interval are in bijection with source 63-bit words
;; through their signed-value observation.

(defconst *bss-min-int63* -4611686018427387904)
(defconst *bss-max-int63* 4611686018427387903)

(defun bss-int63-p (value)
  (and
   (integerp value)
   (<= *bss-min-int63* value)
   (<= value *bss-max-int63*)))

;; Why3 characters are represented by their exact byte codes, and strings by
;; finite lists of those codes.

(defun bss-char-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun bss-string-p (value)
  (if (consp value)
      (and
       (bss-char-p (car value))
       (bss-string-p (cdr value)))
    (equal value nil)))

(defun bss-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun bss-string-index (string index)
  (let ((natural-index
         (bss-int-to-nat index)))
    (if (< natural-index (len string))
        (nth natural-index string)
      0)))

;; Exact finite-list rendering of Why3 substring(text,start,count).

(defun bss-drop-n (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      xs
    (if (consp xs)
        (bss-drop-n (1- count) (cdr xs))
      nil)))

(defun bss-take-n (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp xs)
        (cons
         (car xs)
         (bss-take-n (1- count) (cdr xs)))
      nil)))

(defun bss-substring (text start count)
  (bss-take-n
   (bss-int-to-nat count)
   (bss-drop-n
    (bss-int-to-nat start)
    text)))

;; A finite map is represented by its unique ascending association list of
;; byte keys and signed-63 values.

(defun bss-fmap-entry-p (entry)
  (and
   (consp entry)
   (bss-char-p (car entry))
   (bss-int63-p (cdr entry))))

(defun bss-fmap-tail-p (lower-key entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (and
       (bss-fmap-entry-p (car entries))
       (< lower-key (caar entries))
       (bss-fmap-tail-p
        (caar entries)
        (cdr entries)))
    (equal entries nil)))

(defun bss-fmap-p (map)
  (if (consp map)
      (and
       (bss-fmap-entry-p (car map))
       (bss-fmap-tail-p
        (caar map)
        (cdr map)))
    (equal map nil)))

(defun bss-fmap-member-p (key map)
  (if (assoc-equal key map) t nil))

(defun bss-fmap-lookup (key map)
  (let ((entry (assoc-equal key map)))
    (if entry
        (cdr entry)
      0)))

;; Conservative interfaces preserve the abstract bad-shift-table and map
;; implementation types. Their typing and record invariants are explicit in
;; the final statement predicate.

(defstub bss-bad-shift-table-p (bst) t)
(defstub bss-table-p (table) t)
(defstub bss-pattern (bst) t)
(defstub bss-table (bst) t)
(defstub bss-to-fmap (table) t)

(defun-sk bss-bad-shift-table-domain-nonempty-p ()
  (exists (bst)
    (bss-bad-shift-table-p bst)))

(defun-sk bss-table-domain-nonempty-p ()
  (exists (table)
    (bss-table-p table)))

(defun-sk bss-interface-typed-p ()
  (forall (bst table)
    (and
     (implies
      (bss-bad-shift-table-p bst)
      (and
       (bss-string-p
        (bss-pattern bst))
       (bss-table-p
        (bss-table bst))))
     (implies
      (bss-table-p table)
      (bss-fmap-p
       (bss-to-fmap table))))))

;; The three invariants of Why3's BadShiftTable.bad_shift_table record.

(defun-sk bss-pattern-characters-present-p
    (pattern map)
  (forall (index ch)
    (implies
     (and
      (integerp index)
      (bss-char-p ch)
      (<= 0 index)
      (< index (len pattern))
      (equal ch
             (bss-string-index
              pattern index)))
     (bss-fmap-member-p ch map))))

(defun-sk bss-shift-values-bounded-p
    (pattern map)
  (forall (ch)
    (implies
     (bss-char-p ch)
     (implies
      (bss-fmap-member-p ch map)
      (and
       (<= 1
           (bss-fmap-lookup ch map))
       (<= (bss-fmap-lookup ch map)
           (+ (len pattern) 1)))))))

(defun-sk bss-no-earlier-suffix-character-p
    (pattern map)
  (forall (ch shift)
    (implies
     (and
      (bss-char-p ch)
      (integerp shift)
      (bss-fmap-member-p ch map)
      (<= 1 shift)
      (< shift
         (bss-fmap-lookup ch map)))
     (not
      (equal
       (bss-string-index
        pattern
        (- (len pattern) shift))
       ch)))))

(defun bss-bad-shift-table-invariant-p
    (bst)
  (let* ((pattern (bss-pattern bst))
         (map
          (bss-to-fmap
           (bss-table bst))))
    (and
     (bss-pattern-characters-present-p
      pattern map)
     (bss-shift-values-bounded-p
      pattern map)
     (bss-no-earlier-suffix-character-p
      pattern map))))

(defun-sk bss-invariant-law-p ()
  (forall (bst)
    (implies
     (bss-bad-shift-table-p bst)
     (bss-bad-shift-table-invariant-p
      bst))))

(defun bss-background-p ()
  (and
   (bss-bad-shift-table-domain-nonempty-p)
   (bss-table-domain-nonempty-p)
   (bss-interface-typed-p)
   (bss-invariant-law-p)))

;; The authoritative Why3 predicate uses a substring of length |pattern|.

(defun bss-matches-p (pattern text position)
  (and
   (integerp position)
   (<= 0 position)
   (<= position
       (- (len text)
          (len pattern)))
   (equal
    (bss-substring
     text position (len pattern))
    pattern)))

(defun-sk bss-no-match-anywhere-p
    (pattern text)
  (forall (position)
    (implies
     (integerp position)
     (not
      (bss-matches-p
       pattern text position)))))

(defun bss-result-spec-p
    (pattern text result)
  (and
   (<= -1 result)
   (<= result
       (- (len text)
          (len pattern)))
   (if (equal result -1)
       (bss-no-match-anywhere-p
        pattern text)
     (bss-matches-p
      pattern text result))))

;; This is the loop invariant's quantified no-earlier-match clause.

(defun-sk bss-no-earlier-match-p
    (pattern text upper limit pattern-length)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (and
       (<= 0 position)
       (< position upper))
      (implies
       (<= position limit)
       (not
        (equal
         (bss-substring
          text position pattern-length)
         pattern)))))))

(defun bss-loop-state-p
    (pattern text index n m)
  (and
   (<= 0 index)
   (<= index n)
   (bss-no-earlier-match-p
    pattern text index (- n m) m)))

;; Innermost continuation after the updated search position o5 is introduced.

(defun bss-o5-conclusion-p
    (pattern text m n index o5)
  (and
   (and
    (<= 0
        (- (- n m) index))
    (< (- (- n m) o5)
       (- (- n m) index)))
   (and
    (<= 0 o5)
    (<= o5 n))
   (bss-no-earlier-match-p
    pattern text o5 (- n m) m)))

(defun-sk bss-all-o5-p
    (pattern text m n index shift)
  (forall (o5)
    (implies
     (bss-int63-p o5)
     (implies
      (equal o5
             (+ index shift))
      (bss-o5-conclusion-p
       pattern text m n index o5)))))

(defun bss-o4-antecedent-p
    (map ch m o4)
  (if (bss-fmap-member-p ch map)
      (let ((value
             (bss-fmap-lookup ch map)))
        (and
         (equal o4 value)
         (equal o4 value)))
    (equal o4 (+ m 1))))

(defun bss-o4-conclusion-p
    (pattern text m n index o4)
  (and
   (bss-int63-p
    (+ index o4))
   (bss-all-o5-p
    pattern text m n index o4)))

(defun-sk bss-all-o4-p
    (pattern text map ch m n index)
  (forall (o4)
    (implies
     (bss-int63-p o4)
     (implies
      (bss-o4-antecedent-p
       map ch m o4)
      (bss-o4-conclusion-p
       pattern text m n index o4)))))

(defun bss-o3-conclusion-p
    (pattern text map m n index o3)
  (and
   (and
    (<= 0 o3)
    (< o3 (len text)))
   (let ((ch
          (bss-string-index
           text o3)))
     (and
      (if (bss-fmap-member-p ch map)
          (bss-fmap-member-p ch map)
        (bss-int63-p (+ m 1)))
      (bss-all-o4-p
       pattern text map ch m n index)))))

(defun-sk bss-all-o3-p
    (pattern text map m n index)
  (forall (o3)
    (implies
     (bss-int63-p o3)
     (implies
      (equal o3
             (+ index m))
      (bss-o3-conclusion-p
       pattern text map m n index o3)))))

(defun bss-o2-else-p
    (pattern text map m n index)
  (and
   (bss-int63-p
    (+ index m))
   (bss-all-o3-p
    pattern text map m n index)))

(defun bss-o2-conclusion-p
    (pattern text map m n index o2)
  (if (equal index o2)
      (bss-result-spec-p
       pattern text -1)
    (bss-o2-else-p
     pattern text map m n index)))

(defun-sk bss-all-o2-p
    (pattern text map m n index)
  (forall (o2)
    (implies
     (bss-int63-p o2)
     (implies
      (equal o2
             (- n m))
      (implies
       (implies
        (equal index o2)
        (equal index o2))
       (bss-o2-conclusion-p
        pattern text map m n index o2))))))

(defun bss-nonmatch-branch-p
    (pattern text map m n index)
  (and
   (bss-int63-p
    (- n m))
   (bss-all-o2-p
    pattern text map m n index)))

(defun bss-o1-upper-branch-p
    (pattern text map m n index)
  (and
   (and
    (<= 0 index)
    (<= index
        (- (len text)
           (len pattern))))
   (if (bss-matches-p
        pattern text index)
       (bss-result-spec-p
        pattern text index)
     (bss-nonmatch-branch-p
      pattern text map m n index))))

(defun bss-o1-conclusion-p
    (pattern text map m n index o1)
  (if (<= index o1)
      (bss-o1-upper-branch-p
       pattern text map m n index)
    (bss-result-spec-p
     pattern text -1)))

(defun-sk bss-all-o1-p
    (pattern text map m n index)
  (forall (o1)
    (implies
     (bss-int63-p o1)
     (implies
      (equal o1
             (- n m))
      (bss-o1-conclusion-p
       pattern text map m n index o1)))))

(defun bss-index-conclusion-p
    (pattern text map m n index)
  (and
   (bss-int63-p
    (- n m))
   (bss-all-o1-p
    pattern text map m n index)))

(defun-sk bss-all-indices-p
    (pattern text map m n)
  (forall (index)
    (implies
     (bss-int63-p index)
     (implies
      (bss-loop-state-p
       pattern text index n m)
      (bss-index-conclusion-p
       pattern text map m n index)))))

(defun bss-n-conclusion-p
    (pattern text map m n)
  (and
   (and
    (and
     (<= 0 0)
     (<= 0 n))
    (bss-no-earlier-match-p
     pattern text 0 (- n m) m))
   (bss-all-indices-p
    pattern text map m n)))

(defun-sk bss-all-n-p
    (pattern text map m)
  (forall (n)
    (implies
     (bss-int63-p n)
     (implies
      (and
       (equal n (len text))
       (<= 0 (len text)))
      (bss-n-conclusion-p
       pattern text map m n)))))

(defun-sk bss-all-m-p
    (pattern text map)
  (forall (m)
    (implies
     (bss-int63-p m)
     (implies
      (and
       (equal m (len pattern))
       (<= 0 (len pattern)))
      (bss-all-n-p
       pattern text map m)))))

(defun-sk
    ntp4vc-pearl-string-search-badshifttable-searchqtvc-statement
    ()
  (forall (bst text)
    (implies
     (and
      (bss-background-p)
      (bss-bad-shift-table-p bst)
      (bss-string-p text)
      (<= (len (bss-pattern bst))
          (len text)))
     (bss-all-m-p
      (bss-pattern bst)
      text
      (bss-to-fmap
       (bss-table bst))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
