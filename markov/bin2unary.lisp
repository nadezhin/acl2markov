(in-package "ACL2")
(include-book "markov")
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(defconst *scheme-bin2unary-en*
  (list
    (mk-> '(! 0) '(0 ! !))
    (mk-> '(1)   '(0 !))
    (mk-> '(0)   '())))

(defconst *scheme-bin2unary-ru*
  (list
    (mk-> '(1)   '(0 !))
    (mk-> '(! 0) '(0 ! !))
    (mk-> '(0)   '())))

(define replace-ones
  ((x (wordp x '(0 1))))
  :returns (result (wordp result '(0 !)) :hyp :guard)
  (cond ((atom x) nil)
        ((eql (car x) '1) (list* '0 '! (replace-ones (cdr x))))
        (t (list* (car x) (replace-ones (cdr x)))))
  ///
  (defrule |wordp-of-replace-ones|
    (implies (and (wordp x '(0 1))
                  (true-listp alphabet)
                  (subsetp '(0 !) alphabet))
             (wordp (replace-ones x) alphabet)))
  (defrule |replace-ones append|
    (equal (replace-ones (append x y))
           (append (replace-ones x) (replace-ones y)))
    :induct (len x)))

(define digit-count
  ((x (wordp x '(0 1))))
  :returns (result natp :rule-classes :type-prescription)
  (cond ((atom x) 0)
        ((or (eql (car x) '0) (eql (car x) '1)) (1+ (digit-count (cdr x))))
        (t (digit-count (cdr x))))
  ///
  (defrule |digit-count append|
    (equal (digit-count (append x y))
           (+ (digit-count x) (digit-count y)))))

(define val
  ((x (wordp x '(0 1))))
  :returns (val natp :rule-classes :type-prescription)
  (cond ((atom x) 0)
        ((or (eql (car x) '1) (eql (car x) '!))
         (+ (expt 2 (digit-count (cdr x)))
            (val (cdr x))))
        (t (val (cdr x))))
  ///
  (defrule |val append|
    (equal (val (append x y))
           (+ (val y) (* (val x) (expt 2 (digit-count y)))))
    :enable (digit-count append))
  (defrule |duplicity bar <= val|
    (<= (duplicity '! x)
        (val x))
    :enable duplicity
    :rule-classes :linear)
  (defrule |duplicity 1 <= val|
    (<= (duplicity '1 x)
        (val x))
    :enable duplicity
    :rule-classes :linear))

;-------

(define step1
  ((inp (wordp inp '(0 1)))
   (n (and (natp n) (<= n (len inp)))))
  :returns (result (wordp result '(0 1 !)) :hyp :guard)
  (append (replace-ones (take n inp)) (nthcdr n inp))
  ///
  (defruled |step1 0|
    (equal (step1 inp 0) inp))
  (defruled |step1 len|
    (implies
     (wordp inp '(0 1))
     (equal (step1 inp (len inp))
            (replace-ones inp)))))

(define step2
  ((inp (wordp inp '(0 1)))
   (n (and (natp n) (<= n (len inp)))))
  :returns (result (wordp result '(0 !)) :hyp :guard)
  (append (repeat n '0)
          (repeat (val (take n inp)) '!)
          (replace-ones (nthcdr n inp)))
  ///
  (defruled |step2 0|
    (implies
     (wordp inp '(0 1))
     (equal (step2 inp 0)
            (replace-ones inp))))
  (defruled |step2 len|
    (implies
     (wordp inp '(0 1))
     (equal (step2 inp (len inp))
            (append (repeat (len inp) '0)
                    (repeat (val inp) '!))))))

(define step3
  ((inp (wordp inp '(0 1)))
   (n (and (natp n) (<= n (len inp)))))
  :returns (result (wordp result '(0 !)))
  (append (repeat (- (len inp) n) '0)
          (repeat (val inp) '!))
  ///
  (defruled |step3 0|
    (implies
     (wordp inp '(0 1))
     (equal (step3 inp 0)
            (append (repeat (len inp) '0)
                    (repeat (val inp) '!)))))
  (defruled |step3 len|
    (implies
     (wordp inp '(0 1))
     (equal (step3 inp (len inp))
            (repeat (val inp) '!)))))

(defruled |step2-0 as step1-len|
  (implies
    (wordp inp '(0 1))
    (equal (step2 inp 0)
           (step1 inp (len inp))))
  :enable (|step2 0| |step1 len|))

(defruled |step3-0 as step2-len|
  (implies
    (wordp inp '(0 1))
    (equal (step3 inp 0)
           (step2 inp (len inp))))
  :enable (|step3 0| |step2 len|))

;------

(define cnt
  ((inp (wordp inp '(0 1))))
  :returns (result natp :rule-classes :type-prescription)
  (+ (val inp) (len inp)))

(define step1-cntb
  ((inp (wordp inp '(0 1)))
   (n (and (natp n) (<= n (len inp)))))
  (declare (ignore inp))
  :returns (result natp :rule-classes :type-prescription
                   :hyp (natp n))
  n)

(define step1-cntf
  ((inp (wordp inp '(0 1)))
   (n (and (natp n) (<= n (len inp)))))
  :returns (result natp :rule-classes :type-prescription
                   :hyp (and (natp n) (<= n (len inp))))
  (+ (val inp) (len inp) (- n)))

(defrule |step1 same when 0|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp))
      (eql (nth n inp) '0))
    (equal (step1 inp (1+ n))
           (step1 inp n)))
  :enable (step1 |take n+1| |nthcdr as cons|))

(defruled |step1 applicable when 1|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp))
      (eql (nth n inp) '1))
   (equal
      (applicable *scheme-bin2unary-ru* (step1 inp n))
      (mk-> '(1) '(0 !))))
  :enable (applicable step1)
  :use (:instance sublistp-append-wordp
         (pat '(1))
         (x (replace-ones (take n inp)))
         (alphabet '(0 !))
         (y (nthcdr n inp))))

(defruled |step1 substp when 1|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp))
      (eql (nth n inp) '1))
    (substp (step1 inp n) '(1) '(0 !) (step1 inp (1+ n))))
  :prep-lemmas (
    (defrule lemma
      (implies
        (wordp x '(0 !))
        (left-wingp x '(1)))
      :enable (|left-wingp as left-wingp1| left-wingp1)
      :induct (len x)))
  :enable (step1 |take n+1| |nthcdr as cons|)
  :use (:instance substp-lemma
         (x (step1 inp n))
         (l '(1))
         (r '(0 !))
         (y (step1 inp (1+ n)))
         (lw (replace-ones (take n inp)))
         (rw (nthcdr (1+ n) inp))))

(defruled |step1 correct when 1|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp))
      (eql (nth n inp) '1))
    (simple-stepp
      *scheme-bin2unary-ru*
      (step1 inp n)
      (step1 inp (1+ n))))
  :enable (simple-stepp |step1 applicable when 1| |step1 substp when 1|))

(defruled |step1 correct a|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      (if (eql (nth n inp) '1) 1 0)
      (step1 inp n)
      (step1 inp (1+ n))))
  :enable |step1 correct when 1|
  :disable |nth wordp is member|
  :use (:instance |nth wordp is member|
         (alphabet '(0 1))
         (x inp)
         (i n)))

(defruled |step1 correct all|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (<= n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      (duplicity '1 (take n inp))
      inp
      (step1 inp n)))
  :enable |step1 0|
  :disable duplicity-of-append
  :induct (dec-induct n)
  :hints (("subgoal *1/2" :use ((:instance |step1 correct a|
                                  (n (1- n)))
                                (:instance duplicity-of-append
                                  (a '1)
                                  (x (take (1- n) inp))
                                  (y (list (nth (1- n) inp))))
                                (:instance |take n+1|
                                  (x inp)
                                  (n (1- n)))))))

(defruled |step2 applicable|
  (implies
    (and
      (natp n)
      (posp i)
      (wordp y '(0 !)))
    (equal
      (applicable
        *scheme-bin2unary-ru*
        (append (repeat n '0) (repeat i '!) (cons '0 y)))
      (mk-> '(! 0) '(0 ! !))))
  :prep-lemmas (
    (defrule lemma1
      (implies
        (and (natp n)
             (posp i)
             (wordp y '(0 !)))
        (not (sublistp '(1)
                       (append (repeat n '0)
                               (repeat i '!)
                               (cons '0 y)))))
      :cases ((sublistp '(1) y))
      :hints (("subgoal 1" :use (:instance sublistp-append-wordp
                                  (alphabet '(0 !))
                                  (pat '(1))
                                  (x y)
                                  (y nil)))))
    (defrule lemma2
      (implies
         (posp i)
         (sublistp
           '(! 0)
           (append (repeat i '!) (cons '0 y))))
      :enable (sublistp repeat)
      :induct (dec-induct i)))
  :enable applicable)

(defruled |step2 substp|
  (implies
    (and
      (natp n)
      (posp i)
      (natp j))
    (substp
      (append (repeat n '0) (repeat i '!) (list '0) (repeat j '!) y)
      '(! 0)
      '(0 ! !)
      (append (repeat n '0) (repeat (1- i) '!) (list '0) (repeat (+ 2 j) '!) y)))
  :prep-lemmas (
    (defrule lemma1
      (implies (natp k)
               (left-wingp1 (repeat k '!) '(! 0)))
      :enable (|left-wingp as left-wingp1| left-wingp1)
      :induct (dec-induct k)
      :hints (("subgoal *1/2" :expand (repeat k '!))))
    (defrule lemma2
      (implies
        (and
          (natp n)
          (natp k))
        (left-wingp (append (repeat n '0) (repeat k '!)) '(! 0)))
      :enable (|left-wingp as left-wingp1| left-wingp1)
      :induct (dec-induct n)
      :hints (("subgoal *1/2" :expand (repeat n '0))))
    (defrule lemma3
      (implies
        (natp n)
        (equal (cons a (repeat n a))
               (repeat (1+ n) a)))
     :enable repeat
     :induct (dec-induct n))
   (defrule lemma4
     (implies
       (equal (len x) n)
       (equal (nthcdr n (append x y)) y))
     :induct (cdr-dec-induct x n)))
  :use (:instance substp-lemma
         (x (append (repeat n '0) (repeat i '!) (list '0) (repeat j '!) y))
         (l '(! 0))
         (r '(0 ! !))
         (y (append (repeat n '0) (repeat (1- i) '!) (list '0) (repeat (+ 2 j) '!) y))
         (lw (append (repeat n '0) (repeat (1- i) '!)))
         (rw (append (repeat j '!) y))))

(defruled |step2 correct low|
  (implies
    (and
      (natp n)
      (posp i)
      (natp j)
      (wordp y '(0 !)))
    (simple-stepp
      *scheme-bin2unary-ru*
      (append (repeat n '0) (repeat i '!) (list '0) (repeat j '!) y)
      (append (repeat n '0) (repeat (1- i) '!) (list '0) (repeat (+ 2 j) '!) y)))
  :enable (simple-stepp wordp-repeat2)
  :use ((:instance |step2 applicable|
          (y (append (repeat j '!) y)))
        |step2 substp|))

(defruled |step2 correct a|
  (implies
    (and
      (natp n)
      (natp i)
      (natp j)
      (wordp y '(0 !)))
    (simple-steps
      *scheme-bin2unary-ru*
      i
      (append (repeat n '0) (repeat i '!) (list '0) (repeat j '!) y)
      (append (repeat n '0) (list '0) (repeat (+ (* 2 i) j) '!) y)))
  :prep-lemmas (
    (defrule lemma1
      (implies
        (and
          (natp n)
          (posp i)
          (natp j)
          (wordp y '(0 !)))
        (simple-steps
          *scheme-bin2unary-ru*
          1
          (append (repeat n '0) (repeat i '!) (list '0) (repeat j '!) y)
          (append (repeat n '0) (repeat (1- i) '!) (list '0) (repeat (+ 2 j) '!) y)))
      :disable simple-steps-1
      :use ((:instance simple-steps-1
              (scheme *scheme-bin2unary-ru*)
              (x (append (repeat n '0) (repeat i '!) (list '0) (repeat j '!) y))
              (y (append (repeat n '0) (repeat (1- i) '!) (list '0) (repeat (+ 2 j) '!) y)))
            (:instance |step2 correct low|)))
    (defrule lemma
      (implies
        (and
          (natp n)
          (natp i)
          (natp s)
          (<= (* 2 i) s)
          (wordp y '(0 !)))
        (simple-steps
          *scheme-bin2unary-ru*
          i
          (append (repeat n '0) (repeat i '!) (list '0) (repeat (- s (* 2 i)) '!) y)
          (append (repeat n '0) (list '0) (repeat s '!) y)))
    :induct (dec-induct i)
    :hints (
      ("subgoal *1/2" :use ((:instance lemma1
                              (j (- s (* 2 i)))))))))
  :use (:instance lemma
         (s (+ (* 2 i) j))))

(defrule |val take n+1 inp|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp)))
    (equal (val (take (+ 1 n) inp))
           (+ (* 2 (val (take n inp)))
              (if (eql (nth n inp) 1) 1 0))))
  :enable (|take n+1| digit-count)
  :disable |nth wordp is member|
  :use ((:instance |val append|
          (x (take n inp))
          (y (list (nth n inp))))
        (:instance |nth wordp is member|
          (alphabet '(0 1))
          (x inp)
          (i n))))

(defruled |step2 correct q|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      (val (take n inp))
      (step2 inp n)
      (step2 inp (1+ n))))
  :prep-lemmas (
    (defrule lemma1
      (implies
        (natp n)
        (equal
          (repeat (+ 1 n) a)
          (cons a (repeat n a))))
      :enable repeat)
     (defrule lemma2
       (implies
         (and
           (wordp inp '(0 1))
           (natp n)
           (< n (len inp))
           (not (equal (nth n inp) 1)))
         (equal (cons 0 (replace-ones (nthcdr (+ 1 n) inp)))
                (replace-ones (nthcdr n inp))))
      :enable (|nthcdr as cons| replace-ones))
     (defrule lemma3
       (implies
         (and
           (wordp inp '(0 1))
           (natp n)
           (< n (len inp))
           (equal (nth n inp) 1))
         (equal (list* '0 '! (replace-ones (nthcdr (+ 1 n) inp)))
                (replace-ones (nthcdr n inp))))
      :enable (|nthcdr as cons| replace-ones)))
  :enable step2
  :use (:instance |step2 correct a|
         (i (val (take n inp)))
         (j (if (eql (nth n inp) 1) 1 0))
         (y (replace-ones (nthcdr (1+ n) inp)))))

(define step2-count
  ((inp (wordp inp '(0 1)))
   (n (and (natp n) (<= n (len inp)))))
  :returns (result natp :rule-classes :type-prescription)
  (- (val (take n inp))
     (duplicity '1 (take n inp)))
  ///
  (defrule step2-count-0
    (equal (step2-count inp 0) 0))
  (defruled step2-count-diff
    (implies (and (wordp inp '(0 1))
                  (posp n)
                  (<= n (len inp)))
             (equal (- (step2-count inp n)
                       (step2-count inp (1- n)))
                    (val (take (1- n) inp))))
    :use ((:instance duplicity-of-append
            (a '1)
            (x (take (+ -1 n) inp))
            (y (list (nth n inp))))
          (:instance |val take n+1 inp|
            (n (1- n)))
          (:instance |take n+1|
            (x inp)
            (n (1- n))))))

(defruled |step2 correct 4|
  (implies
   (and
    (wordp inp '(0 1))
    (natp n)
    (<= n (len inp)))
   (simple-steps
    *scheme-bin2unary-ru*
    (step2-count inp n)
      (step2 inp 0)
      (step2 inp n)))
  :enable step2-count-diff
  :induct (dec-induct n)
  :hints (("subgoal *1/2" :use ((:instance |step2 correct q|
                                  (n (1- n)))))))

#|
(step2 '(1 0 1) 0)
(step2 '(1 0 1) 1)
(step2 '(1 0 1) 2)
(step2 '(1 0 1) 3)
|#
(defruled |step1 and step2 correct|
  (implies
    (wordp inp '(0 1))
    (simple-steps
      *scheme-bin2unary-ru*
      (val inp)
      inp
      (append (repeat (len inp) '0)
              (repeat (val inp) '!))))
  :enable (|step2-0 as step1-len| |step2 len| step2-count)
  :use ((:instance |step1 correct all|
          (n (len inp)))
        (:instance |step2 correct 4|
          (n (len inp)))))

(defruled |step3 applicable|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp)))
   (equal
      (applicable *scheme-bin2unary-ru* (step3 inp n))
      (mk-> '(0) '())))
  :prep-lemmas (
    (defrule lemma1
      (not (sublistp '(1) (repeat n '!)))
      :enable (sublistp repeat)
      :induct (dec-induct n))
    (defrule lemma2
      (not (equal '0 (car (repeat n '!))))
      :enable repeat)
    (defrule lemma3
      (implies
        (natp n)
        (not (sublistp '(! 0) (repeat n '!))))
      :enable (sublistp repeat prefixp)
      :induct (dec-induct n))
    (defrule lemma4
      (implies
        (posp n)
        (sublistp '(0) (append (repeat n '0) x)))
      :expand (repeat n '0)))
  :enable (applicable step3))

(defruled |step3 substp|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (< n (len inp)))
    (substp
      (step3 inp n)
      '(0)
      '()
      (step3 inp (1+ n))))
  :prep-lemmas (
    (defrule lemma
      (implies (equal n (len x))
               (equal (nthcdr n (append x y)) y))))
  :enable (step3 repeat)
  :use (:instance substp-lemma
         (x (step3 inp n))
         (l '(0))
         (r '())
         (y (step3 inp (1+ n)))
         (lw '())
         (rw (step3 inp (1+ n)))))

(defruled |step3 correct a|
  (implies
    (and
      (wordp inp '(0 1))
      (posp n)
      (<= n (len inp)))
    (simple-stepp
      *scheme-bin2unary-ru*
      (step3 inp (1- n))
      (step3 inp n)))
  :enable (simple-stepp |step3 applicable|)
  :use (:instance |step3 substp|
         (n (1- n))))

(defruled |step3 correct b|
  (implies
    (and
      (wordp inp '(0 1))
      (natp n)
      (<= n (len inp)))
    (simple-steps
      *scheme-bin2unary-ru*
      n
      (step3 inp 0)
      (step3 inp n)))
  :enable |step3 correct a|
  :induct (dec-induct n))

(defruled |step123 correct|
  (implies
    (wordp inp '(0 1))
    (simple-steps
     *scheme-bin2unary-ru*
     (cnt inp)
     inp
     (repeat (val inp) '!)))
  :enable (|step2 len| |step3 0| |step3 len| cnt)
  :use (|step1 and step2 correct|
        (:instance |step3 correct b|
          (n (len inp)))))

(defruled |applicable final|
  (not (applicable *scheme-bin2unary-ru* (repeat n '!)))
  :enable (applicable repeat)
  :induct (dec-induct n))
