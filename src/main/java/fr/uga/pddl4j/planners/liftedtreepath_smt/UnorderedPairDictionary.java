package fr.uga.pddl4j.planners.liftedtreepath_smt;

import java.util.HashMap;
import java.util.Map;
import org.apache.commons.lang3.tuple.Pair;

public class UnorderedPairDictionary<K, V> {
    private Map<Pair<K, K>, V> dictionary;

    public UnorderedPairDictionary() {
        dictionary = new HashMap<>();
    }

    public void put(K key1, K key2, V value) {
        Pair<K, K> key = keyPair(key1, key2);
        dictionary.put(key, value);
    }

    public V get(K key1, K key2) {
        Pair<K, K> key = keyPair(key1, key2);
        return dictionary.get(key);
    }

    public boolean containsKey(K key1, K key2) {
        Pair<K, K> key = keyPair(key1, key2);
        return dictionary.containsKey(key);
    }

    private Pair<K, K> keyPair(K key1, K key2) {
        if (key1.hashCode() < key2.hashCode()) {
            return Pair.of(key1, key2);
        } else {
            return Pair.of(key2, key1);
        }
    }
}