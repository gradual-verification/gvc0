package gvc.benchmarking

import gvc.benchmarking.NetworkingUtilities.Message

class BenchmarkNode {

  def listen(): Unit = {
    // called from main.scala
    // sets up networking layer
    // repeatedly waits and tries to connect to the specified server IP/port
    // done in a while loop forever.
  }
  /*
  //passed as the handleJob parameter to ClientNetworkingLayer
  def runBenchmark(request: Message): Message = {
    //Run in a loop:
    // I have a IP and a Port # to listen for a program from
    // I'm receiving something that contain the following information:
    // * iterations
    // * workload for running programs
    // * source code of the program that I need to run

    // verify
    // execute

    //(this will probably be handled in NetworkingLayer.scala): send a response back to the IP and Port # with all data.
  }*/
}
