predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	if (|pre| == 0)
	{
		return true;
	}
	if (|str| < |pre|)
	{
		return false;
	}
	return str[..|pre|] == pre;
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	ensures !res <==> isNotSubstringPred(sub, str) 
{
	res := false;
	var i := 0;
	while (i <= |str| && !res)
		invariant 0 <= i <= |str| + 1
		invariant !res <==> (forall j :: (0 <= j < i ==> isNotPrefixPred(sub, str[j..])))
		decreases |str| - i
	{
		var prefix := isPrefix(sub, str[i..]);
		if (prefix) {
			res := true;
		}
		i := i + 1;
	}
	return res;
}

predicate haveCommonKSubstringPred(x:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- x && j1 == i1 + x && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(x:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- x && j1 == i1 + x ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(x:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(x,str1,str2) <==> !haveNotCommonKSubstringPred(x,str1,str2)
	ensures !haveCommonKSubstringPred(x,str1,str2) <==>  haveNotCommonKSubstringPred(x,str1,str2)
{}

method haveCommonKSubstring(x: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(x, str1, str2)
	ensures !found <==> haveNotCommonKSubstringPred(x,str1,str2) 
{
	if (|str1| < x) {
		return false;
	}
	found := false;
	var i := 0;
	while (i <= |str1| - x && !found)
		invariant |str1| >= x ==> 0 <= i <= |str1| - x + 1
		invariant !found <==> forall j, j1 :: (0 <= j < i && j1 == j + x ==> isNotSubstringPred(str1[j..j1], str2))
		decreases |str1| - i
	{
		var index := i + x;
		var substring := isSubstring(str1[i..index], str2);
		if (substring) {
			found := true;
		}
		i := i + 1;
	}
	return found;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
	requires (|str1| <= |str2|)
	ensures (forall x :: len < x <= |str1| ==> !haveCommonKSubstringPred(x, str1, str2))
	ensures haveCommonKSubstringPred(len, str1, str2)
{
	len := |str1|;

	while (len > 0)
		invariant forall x :: (len < x <= |str1| ==> !haveCommonKSubstringPred(x, str1, str2))
		decreases len
	{
		var found := haveCommonKSubstring(len, str1, str2);
		if (found) {
			return len;
		}
		len := len - 1;
	}
	assert isPrefixPred(str1[0..0], str2[0..]);
	return len;
}
