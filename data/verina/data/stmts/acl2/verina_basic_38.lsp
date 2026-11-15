;; Statement-only formalization of VERINA corpus artifact verina_basic_38,
;; catalog title "allCharactersSame": a deterministic Unicode-string program
;; returns true exactly when all characters are identical, including empty and
;; singleton strings. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain rather than restricting
;; strings to ACL2's host character set.

(defun verina-basic-38-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-38-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-38-unicode-scalar-p (car s))
       (verina-basic-38-string-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The String binder domain remains explicit
;; in the final correctness statement.

(defun verina-basic-38-all-characters-same-precond (s)
  (declare (ignore s))
  t)

;; This is the source implementation's cs.all (fun x => x = c), where C is
;; the first character and REMAINING is the tail of the represented string.

(defun verina-basic-38-all-equal-to-p (remaining c)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (equal (car remaining) c)
       (verina-basic-38-all-equal-to-p
        (cdr remaining)
        c))
    t))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The empty branch returns true; the nonempty branch performs
;; exactly the source tail scan against the first character.

(defun verina-basic-38-all-characters-same (s)
  (if (consp s)
      (verina-basic-38-all-equal-to-p
       (cdr s)
       (car s))
    t))

(defun verina-basic-38-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; List.Pairwise equality requires each head to equal every later element and
;; recursively imposes the same requirement on the tail.

(defun verina-basic-38-head-equal-to-all-p (c remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (equal c (car remaining))
       (verina-basic-38-head-equal-to-all-p
        c
        (cdr remaining)))
    t))

(defun verina-basic-38-pairwise-equal-p (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (and
       (verina-basic-38-head-equal-to-all-p
        (car characters)
        (cdr characters))
       (verina-basic-38-pairwise-equal-p
        (cdr characters)))
    (equal characters nil)))

;; Char.get! at index zero returns the first character when present and the
;; inhabited Unicode NUL default on an empty list.

(defun verina-basic-38-first-default-nul (characters)
  (if (consp characters)
      (car characters)
    0))

;; This recursion is exactly cs.any (fun x => x != cs[0]!).

(defun verina-basic-38-any-different-from-p
    (characters reference)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (or
       (not (equal (car characters) reference))
       (verina-basic-38-any-different-from-p
        (cdr characters)
        reference))
    nil))

;; This is the complete source postcondition. ACL2 t/nil are the two Boolean
;; values, so its implications reproduce the source Bool-to-Prop coercions.

(defun verina-basic-38-all-characters-same-postcond
    (s result)
  (and
   (verina-basic-38-string-p s)
   (verina-basic-38-bool-p result)
   (implies
    result
    (verina-basic-38-pairwise-equal-p s))
   (implies
    (not result)
    (and
     (not (equal s nil))
     (verina-basic-38-any-different-from-p
      s
      (verina-basic-38-first-default-nul s))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every Unicode string, applies the source's True precondition, and
;; connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-38-all-characters-same-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-38-string-p s)
      (verina-basic-38-all-characters-same-precond s))
     (verina-basic-38-all-characters-same-postcond
      s
      (verina-basic-38-all-characters-same s)))))

(value-triple :itpeval-statement-checked)
:q
