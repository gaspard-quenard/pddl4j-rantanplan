package fr.uga.pddl4j.planners.lilotane;

import java.util.Vector;

/*
 * A tree rex layer. Contains an array of element. 
 */
public class Layer {
    public Vector<Integer> e;
    public Vector<Integer> n;
    public Vector<LayerElement> layerElements;
    public Layer(){
        e = new Vector<>();
        n = new Vector<>();
        layerElements = new Vector<LayerElement>();
    }
    public String layerToString(){
        return "-----------------\ne : " + e.toString() + "\nn : " + n.toString() + "\n-----------------\n";
    }
}