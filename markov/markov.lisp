(in-package "ACL2")
(include-book "std/lists/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(local (include-book "std/basic/inductions" :dir :system))

(defrule |sublistp when listpos|
  (implies (listpos x y) (sublistp x y)))

(defruled |take n+1|
  (implies
    (and
      (true-listp x)
      (natp n)
      (< n (len x)))
    (equal (take (+ 1 n) x)
           (append (take n x) (list (nth n x)))))
  :induct (cdr-dec-induct x n))

(defruled |nthcdr n+1|
  (implies
    (natp n)
    (equal (nthcdr (+ 1 n) x)
           (cdr (nthcdr n x))))
  :enable nthcdr
  :induct (cdr-dec-induct x n))

(defrule nthcdr-len
  (implies (true-listp x)
           (equal (nthcdr (len x) x)
                  nil));
    :enable nthcdr
    :induct (len x)
    :do-not generalize)

(defruled |nthcdr as cons|
  (implies
    (and
      (natp n)
      (< n (len x)))
    (equal (nthcdr n x)
           (cons (nth n x) (nthcdr (1+ n) x))))
  :enable |nthcdr n+1|
  :disable consp-of-nthcdr
  :use consp-of-nthcdr)

(defruled prefixp-append
  (equal (prefixp x (append y z))
         (if (<= (len x) (len y))
             (prefixp x y)
             (and (equal (take (len y) x) (list-fix y))
                  (prefixp (nthcdr (len y) x) z))))
  :enable (prefixp len |nthcdr n+1|)
  :induct (cdr-cdr-induct x y)) 

(defrule prefixp-transitive
  (implies
    (and (prefixp x y) (prefixp y z))
    (prefixp x z))
  :prep-lemmas (
    (defrule lemma
      (implies
        (prefixp x y)
        (equal (append x (nthcdr (len x) y)) y))
      :enable (prefixp append len |nthcdr n+1|)
      :induct (cdr-cdr-induct x y)
      :rule-classes ()))
  :use ((:instance lemma
          (x x)
          (y y))
        (:instance lemma
          (x y)
          (y z)))
  :rule-classes ())

(define wordp
  ((x t)
   (alphabet true-listp))
  :returns (b booleanp :rule-classes :type-prescription)
  (and (true-listp alphabet) (true-listp x) (subsetp-equal x alphabet)))

(defrule |alphabet when wordp|
  (implies (wordp x alphabet) (true-listp alphabet))
  :enable wordp)

(defrule |wordp is true-listp|
  (implies (wordp x alphabet) (true-listp x))
  :enable wordp)

(defrule |nil is wordp|
  (implies
    (true-listp alphabet)
    (wordp nil alphabet))
  :enable wordp)

(defrule |nth wordp is member|
  (implies (and (wordp x alphabet)
                (natp i)
                (< i (len x)))
           (member (nth i x) alphabet))
  :enable wordp
  :induct (len x))

(defrule wordp-cons
  (equal
    (wordp (cons a x) alphabet)
    (and (member a alphabet)
         (wordp x alphabet)))
  :enable wordp)

(defrule wordp-take
  (implies
    (and
      (wordp x alphabet)
      (<= n (len x)))
    (wordp (take n x) alphabet))
  :enable take-redefinition
  :induct (cdr-dec-induct x n)) 

(defrule wordp-nthcdr
  (implies
    (wordp x alphabet)
    (wordp (nthcdr n x) alphabet))
  :enable (wordp nthcdr)
  :induct (cdr-dec-induct x n)) 

(defrule listpos-append-wordp
  (implies
    (and
      (wordp x alphabet)
      (consp pat)
      (not (member (car pat) alphabet)))
    (equal (listpos pat (append x y))
           (and (listpos pat y)
                (+ (len x) (listpos pat y)))))
  :enable listpos
  :induct (len x))

(defrule sublistp-append-wordp
  (implies
    (and
      (wordp x alphabet)
      (not (member (car pat) alphabet)))
    (equal (sublistp pat (append x y))
           (sublistp pat y)))
  :induct (len x))

(defund mks-> (l r)
  (declare (xargs :guard (and (stringp l) (stringp r))))
  (cons (coerce l 'list) (cons (coerce r 'list) nil)))

(defund mks->. (l r)
  (declare (xargs :guard (and (stringp l) (stringp r))))
  (cons (coerce l 'list) (cons (coerce r 'list) t)))

(defund left-wing (x y)
  (declare (xargs :guard t))
  (cond ((prefixp x y) nil)
        ((atom y) nil)
        (t (cons (car y) (left-wing x (cdr y))))))

(defrule |left-wing when not sublistp|
  (implies (not (sublistp x y))
           (equal (left-wing x y)
                  (list-fix y)))
  :enable left-wing)

(defruled |left-wing as take|
  (equal (left-wing x y)
         (if (sublistp x y)
             (take (listpos x y) y)
             (list-fix y)))
  :enable (sublistp left-wing listpos))

(defruled |len left-wing|
  (equal (len (left-wing x y))
         (if (sublistp x y)
             (listpos x y)
             (len y)))
  :enable (left-wing listpos))

(defrule |prefixp left-wing|
  (prefixp (left-wing x y) y)
  :enable left-wing)

(defund right-wing (x y)
  (declare (xargs :guard t))
  (cond ((prefixp x y) (rest-n (len x) y))
        ((atom y) y)
        (t (right-wing x (cdr y)))))

(defrule |right-wing when not sublistp|
  (implies (not (sublistp x y))
           (equal (right-wing x y)
                  (final-cdr y)))
  :enable right-wing)

(defruled |len right-wing|
  (equal (len (right-wing x y))
         (if (sublistp x y)
             (+ (len y) (- (listpos x y)) (- (len x)))
             0))
  :enable (right-wing listpos))

(defrule rule-cat-before
  (implies (sublistp x y)
           (equal y
                  (append (left-wing x y)
                          x
                          (right-wing x y))))
  :prep-lemmas (
    (defrule lemma
      (implies (prefixp x y)
               (equal (append x (nthcdr (len x) y))
                      y))
     :enable (prefixp append nthcdr len)))
  :enable (sublistp left-wing right-wing)
  :rule-classes ())

(defund substitute-first (l r x)
  (declare (xargs :guard (true-listp r)))
  (append (left-wing l x) r (right-wing l x)))

(defund substitute-first-alt (l r x)
  (cond ((prefixp l x) (append r (nthcdr (len l) x)))
        ((atom x) x)
        (t (cons (car x)
                 (substitute-first-alt l r (cdr x))))))

(defruled |substitute-first as substitute-first-alt|
  (implies
    (sublistp l x)
    (equal (substitute-first l r x)
           (substitute-first-alt l r x)))
  :enable (substitute-first
           left-wing right-wing
           substitute-first-alt))

(defruled rule-cat-after
  (implies (sublistp l y)
           (equal (substitute-first l r y)
                  (append (left-wing l y)
                          r
                          (right-wing l y))))
 :enable substitute-first)

(defund rulep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (consp (cdr x))
       (true-listp (car x))
       (true-listp (cadr x))
       (booleanp (cddr x))))
 
(defund schemep (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (rulep (car x))
           (schemep (cdr x)))))

(defund applicable (scheme x)
  (declare (xargs :guard (schemep scheme)
                  :guard-hints (("goal" :in-theory (enable schemep rulep)))))
  (cond ((atom scheme) nil)
        ((sublistp (caar scheme) x) (car scheme))
        (t (applicable (cdr scheme) x))))

(defrule |sublistp when applicable|
  (implies
    (applicable scheme x)
    (sublistp (car (applicable scheme x)) x))
  :enable applicable)

(defund apply-rule (rule x)
  (if rule
      (substitute-first (car rule) (cadr rule) x)
      x))

(defund apply-scheme (scheme x)
  (declare (xargs :guard (schemep scheme)
                  :guard-hints (("goal" :in-theory (enable schemep applicable rulep)))))
  (let ((rule (applicable scheme x)))
       (if rule
           (substitute-first (car rule) (cadr rule) x)
           x)))

(defund apply-scheme-alt (scheme x)
  (let ((rule (applicable scheme x)))
       (if rule
           (substitute-first-alt (car rule) (cadr rule) x)
           x)))

(defruled |apply-scheme as apply-scheme-alt|
  (equal (apply-scheme scheme x)
         (apply-scheme-alt scheme x))
  :enable (apply-scheme apply-scheme-alt
           |substitute-first as substitute-first-alt|))

(defund markov-trace-aux (trace top scheme n)
  (declare (xargs :measure (nfix n)))
  (let* ((rule (applicable scheme top))
         (next (apply-rule rule top)))
        (cond ((not rule) (rev trace))
              ((zp n) nil)
              ((cddr rule) (rev (cons (coerce next 'string) trace)))
              (t (markov-trace-aux (cons (coerce next 'string) trace)
                                   next
                                   scheme
                                   (1- n))))))

(defund markov-trace (scheme str n)
  (markov-trace-aux (list str) (coerce str 'list) scheme n))

(defund left-wingp (x pat)
  (declare (xargs :guard (true-listp x)))
  (equal (listpos pat (append x pat))
         (len x)))

(defund left-wingp1 (x pat)
  (declare (xargs :guard (true-listp x)))
  (cond ((atom x) t)
        ((prefixp pat (append x pat)) nil)
        (t (left-wingp1 (cdr x) pat))))

(defruled |left-wingp as left-wingp1|
  (equal
    (left-wingp x pat)
    (left-wingp1 x pat))
  :enable (left-wingp left-wingp1 listpos)
  :induct (len x))

(defruled |left-wingp correct|
  (implies
    (left-wingp lw pat)
    (and
      (equal (left-wing pat (append lw pat rw)) (list-fix lw))
      (equal (right-wing pat (append lw pat rw)) rw)))
  :prep-lemmas (
    (defrule lemma1
      (equal (nthcdr (len pat) (append pat rw)) rw)
      :induct (len pat))
    (defrule lemma2
      (implies
        (and
          (prefixp pat (append lw pat rw))
        )
        (prefixp pat (append lw pat)))
      :enable prefixp-append))
  :enable (|left-wingp as left-wingp1| left-wingp1 left-wing right-wing)
  :induct (len lw))

(defund substp (x l r y)
  (declare (xargs :guard (true-listp r)))
  (equal (substitute-first l r x) y))

(defrule substp-lemma
  (implies
    (and
      (left-wingp lw l)
      (equal (append lw l rw) x)
      (equal (append lw r rw) y))
    (substp x l r y))
  :enable (substp substitute-first |left-wingp correct|)
  :rule-classes ())

(defund simple-stepp (scheme x y)
  (declare (xargs :guard (schemep scheme)
                  :guard-hints (("goal" :in-theory (enable schemep applicable rulep)))))
  (let ((rule (applicable scheme x)))
       (and rule
            (not (cddr rule))
            (substp x (car rule) (cadr rule) y))))

(defund simple-steps (scheme n x y)
  (declare (xargs :guard (and (schemep scheme) (natp n))
                  :guard-hints (("goal" :in-theory (enable schemep applicable rulep)))))
  (let ((rule (applicable scheme x)))
    (if (zp n)
        (equal x y)
        (and rule
             (not (cddr rule))
             (simple-steps scheme (1- n) (apply-scheme scheme x) y)))))

(defrule simple-steps-0
  (simple-steps scheme 0 x x)
  :enable simple-steps)

(defrule simple-steps-1
  (implies (simple-stepp scheme x y)
           (simple-steps scheme 1 x y))
  :enable (simple-stepp apply-scheme simple-steps substp))

(defrule simple-steps-cat
  (implies
    (and
      (natp m)
      (natp n)
      (simple-steps scheme m x y)
      (simple-steps scheme n y z))
    (simple-steps scheme (+ m n) x z))
  :enable simple-steps
  :induct (simple-steps scheme m x y)
  :rule-classes ())
